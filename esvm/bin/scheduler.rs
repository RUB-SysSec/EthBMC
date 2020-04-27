extern crate clap;
extern crate esvm;
extern crate fern;
extern crate ethereum_newtypes;
extern crate rayon;
extern crate regex;
extern crate reqwest;
extern crate hexdecode;
extern crate serde_json;

#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate log;
extern crate chrono;

use std::fs::{self, File};
use std::io::{BufWriter, Read, Write};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc, Mutex,
};
use std::thread;
use std::time::Duration;

use esvm::{AttackType, TimeoutAnalysis, AnalysisSuccess};

use serde_json::json;
use chrono::prelude::Local;
use clap::{App, Arg, ArgMatches};
use ethereum_newtypes::{Address};
use regex::Regex;
use reqwest::Client;

fn init_logger() -> Result<()> {
    fern::Dispatch::new()
        // Perform allocation-free log formatting
        .format(|out, message, record| {
            out.finish(format_args!(
                "{}[{}][{}] {}",
                chrono::Local::now().format("[%Y-%m-%d][%H:%M:%S]"),
                record.target(),
                record.level(),
                message
            ))
        })
        // Add blanket level filter -
        .level(log::LevelFilter::Info)
        // Output to stdout, files, and other Dispatch configurations
        .chain(std::io::stdout())
        .chain(fern::log_file("log/evmse-scheduler.log")?)
        // Apply globally
        .apply()?;
    Ok(())
}

#[derive(Debug)]
struct Worker {
    client: Client,
    url: String,
    timeout: Duration,
}

impl Worker {
    fn new(url: &str, timeout: usize) -> Result<Worker> {
        let client = reqwest::Client::builder().timeout(None).build()?;
        let mut url = format!("{}/analyze_address", url);
        if timeout > 0 {
            url.push_str("_timeout");
        }
        let timeout = Duration::from_secs((timeout * 60) as u64);
        Ok(Worker {
            client,
            url: url,
            timeout,
        })
    }

    fn analyze(&self, address: Address) -> Result<AnalysisSuccess> {
        info!("Analyzing {:x}", address.0);
        let mut res = if self.timeout > Duration::from_secs(0) {
            self
            .client
            .post(&self.url)
            .json(&TimeoutAnalysis { address, timeout: self.timeout})
            .send()?
        } else {
            self
            .client
            .post(&self.url)
            .json(&address)
            .send()?
        };
         Ok(res.json()?)
    }

    fn check_alive(&self) -> Result<()> {
        self.client
            .get(&format!("{}/alive", &self.url))
            .send()
            .map_err(|e| e.into())
            .map(|_| ())
    }
}

struct WorkerHandle<'a> {
    worker: Option<Worker>,
    scheduler: &'a Scheduler,
    kill: bool,
}

impl<'a> WorkerHandle<'a> {
    // specifically consume the handle to force readding the worker
    fn analyze(mut self, addr: Address) -> Result<AnalysisSuccess> {
        let res = self.worker.as_ref().unwrap().analyze(addr);
        if let Err(ref error) = res {
            error!("Error analyzing {:x?}, checking worker!", error);
            if let Err(_) = self.worker.as_ref().unwrap().check_alive() {
                error!("Worker died analyzing {:x?}, shuting down worker!", error);
                self.kill = true;
            } else {
                return Err(Error::retry());
            }
        }
        res
    }
}

impl<'a> Drop for WorkerHandle<'a> {
    fn drop(&mut self) {
        if !self.kill {
            let worker = self
                .worker
                .take()
                .expect("Worker replaced before adding back");
            self.scheduler.add_worker(worker)
        } else {
            self.worker
                .take()
                .expect("Worker replaced before adding back");
        }
    }
}

#[derive(Debug)]
struct Scheduler {
    queue: Arc<Mutex<Vec<Worker>>>,
}

impl Scheduler {
    fn new() -> Self {
        let queue = Arc::new(Mutex::new(Vec::new()));
        Self { queue }
    }

    fn with_worker_count(urls: Vec<String>, timeout: usize) -> Self {
        let s = Scheduler::new();
        for url in &urls {
            s.queue.lock().unwrap().push(Worker::new(url, timeout).unwrap()); // if the workers can not connect initially fail
        }
        s
    }

    fn add_worker(&self, worker: Worker) {
        self.queue.lock().unwrap().push(worker);
    }

    fn get_worker(&self) -> WorkerHandle {
        let worker;
        loop {
            if let Some(w) = self.queue.lock().unwrap().pop() {
                worker = Some(w);
                break;
            }
        }
        WorkerHandle {
            worker,
            scheduler: self,
            kill: false,
        }
    }
}

type Result<T> = ::std::result::Result<T, Error>;

#[derive(Debug)]
struct Error {
    kind: Kind,
}

impl Error {
    fn from_str(s: String) -> Self {
        Self {
            kind: Kind::Execution(s),
        }
    }

    fn retry() -> Self {
        Self {
            kind: Kind::Retry,
        }
    }

    fn kind(&self) -> &Kind {
        &self.kind
    }
}

macro_rules! impl_error_kind {
    (
        $(#[$struct_attr:meta])*
        enum Kind {
            $( $enum_variant_name:ident($error_type:path), )+ ;
            $( $single_variant_name:ident, )+
        }
        ) => {
        // meta attributes
        $(#[$struct_attr])*
        // enum definition
        enum Kind {
            $( $enum_variant_name($error_type), )+
            $( $single_variant_name, )+
        }

        // impl error conversion for each type
        $(
            impl ::std::convert::From<$error_type> for Error {
                fn from(error: $error_type) -> Self {
                    Self {
                        kind: Kind::$enum_variant_name(error),
                    }
                }
            }
            )+
    };
}

impl_error_kind!(#[derive(Debug)]
enum Kind {
    Reqwest(reqwest::Error),
    SerdeJson(serde_json::Error),
    Log(log::SetLoggerError),
    IO(std::io::Error),
    Execution(String), ; 
    Retry,
});

fn parse_args<'a>() -> ArgMatches<'a> {
    App::new("EthAEG scheduler for analyzing a large list of contracts")
        .arg(
            Arg::with_name("INPUT")
                .help("Set the list of accounts to scan")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("SERVER_LIST")
                .help("Set the list of backend servers")
                .required(true)
                .index(2),
        )
        .arg(Arg::with_name("timeout").long("timeout").takes_value(true).help("Specify a timeout for the analysis, none used by default"))
        .arg(Arg::with_name("json").long("json").help("Dump the analysis result in json format."))
        .get_matches()
}

fn parse_account_list(path: &str) -> (Arc<Mutex<Vec<(usize, String)>>>, usize) {
    let mut acc_list = String::new();
    File::open(path)
        .expect("Could not open account list")
        .read_to_string(&mut acc_list)
        .expect("Could not read account list");
    let acc_vec: Vec<(usize, String)> = acc_list
        .lines()
        .filter_map(|line| match ACC_RE.captures(line) {
            Some(cap) => {
                let capture = cap.get(0).unwrap().as_str();
                Some((0, capture.to_string()))
            }
            None => {
                warn!("Could not process: {}", line);
                None
            }
        })
        .collect();
    let len = acc_vec.len();
    (Arc::new(Mutex::new(acc_vec)), len)
}

fn parse_server_list(path: &str) -> Vec<String> {
    let mut server_list = String::new();
    File::open(path)
        .expect("Could not open server list")
        .read_to_string(&mut server_list)
        .expect("Could not read server list");
    server_list
        .lines()
        .map(|line| {
            let line = line.trim();
            if line.starts_with("http") || line.starts_with("https") {
                line.to_string()
            } else {
                format!("http://{}", line)
            }
        })
        .collect()
}

lazy_static! {
    static ref ACC_RE: Regex = Regex::new(r"0x[A-za-z0-9]{40}").unwrap();
}

fn execute(
    work_stack: Arc<Mutex<Vec<(usize, String)>>>,
    scheduler: Arc<Scheduler>,
    counter: Arc<AtomicUsize>,
    acc_len: usize,
    root_path: Arc<String>,
    csv: &Mutex<BufWriter<File>>,
    json: bool,
) -> Result<()> {
    loop {
        let (c, acc) = match work_stack.lock().unwrap().pop() {
            Some(work) => work,
            None => {
                info!("Could not fetch new work, exiting loop!");
                return Ok(());
            }
        };

        if c >= 5 {
            info!("Account {} seed {} times, discarding!", acc, c);
            continue;
        }

        let a = Address(hexdecode::decode(&acc.as_bytes()).unwrap().as_slice().into());
        let worker = scheduler.get_worker();
        let res = worker.analyze(a);

        match res {
            Ok(r) => {
                let file_path = if json {
                    format!("{}/{}.json", root_path, acc)
                } else {
                    format!("{}/{}", root_path, acc)
                };
                let mut f = match File::create(file_path) {
                    Ok(f) => f,
                    Err(e) => {
                        error!("Could not create file for {}: {:?}", acc, e);
                        return Err(Error::from_str(format!(
                            "Could not create file for {}: {:?}",
                            acc, e
                        )));
                    }
                };
                if json {
                    if let AnalysisSuccess::Success(ref analysis) = r {
                            let mut res = (false, false, false);
                            if let Some(ref attacks) = analysis.attacks {
                                for attack in attacks {
                                    if attack.attack_type == AttackType::StealMoney {
                                        res.0 = true;
                                    }
                                    if attack.attack_type == AttackType::DeleteContract {
                                        res.1 = true;
                                    }
                                    if attack.attack_type == AttackType::HijackControlFlow {
                                        res.2 = true;
                                    }
                                }
                            }
                            csv.lock().unwrap().write_all(format!("{:x}, {}, {}, {}\n", analysis.address, res.0, res.1, res.2).as_bytes()).expect("Could not write to csv file!");

                    }
                    let _write_res = f.write_all(json!(r).to_string().as_bytes());
                } else {
                    let content = match r {
                        AnalysisSuccess::Success(analysis) => {
                            let mut res = (false, false, false);
                            if let Some(ref attacks) = analysis.attacks {
                                for attack in attacks {
                                    if attack.attack_type == AttackType::StealMoney {
                                        res.0 = true;
                                    }
                                    if attack.attack_type == AttackType::DeleteContract {
                                        res.1 = true;
                                    }
                                    if attack.attack_type == AttackType::HijackControlFlow {
                                        res.2 = true;
                                    }
                                }
                            }
                            csv.lock().unwrap().write_all(format!("{:x}, {}, {}, {}\n", analysis.address, res.0, res.1, res.2).as_bytes()).expect("Could not write to csv file!");

                            format!("{}", analysis)
                        },
                        AnalysisSuccess::Failure(s) => {
                            warn!("Failure during analysing {}: {}", acc, s);
                            s
                        },
                        AnalysisSuccess::Timeout => {
                            warn!("Timeout during analysis: {:?}", acc);
                            format!("Timeout analysing {:?}", acc)
                        },
                    };
                    let _write_res = f.write_all(content.as_bytes());
                }
            }
            Err(e) => {
                if let Kind::Retry = e.kind() {
                    error!("Error analyzing {}, retrying...", acc);
                    work_stack.lock().unwrap().push((c+1, acc));
                } else {
                    error!("Error analyzing {}: {:?} worker died!", acc, e);
                }
            }
        };
        info!(
            "Analyzed {} of {} contracts",
            counter.fetch_add(1, Ordering::Relaxed),
            acc_len
        );
    }
}

fn main() {
    // init logger
    init_logger().expect("Could not initialize logger");

    // parse args
    let matches = parse_args();

    // create root path
    let root_path = format!(
        "analysis/{}/",
        Local::now().format("%Y-%m-%d-%H:%M:%S").to_string()
    );
    fs::create_dir_all(root_path.clone()).expect("Could not create root folder for analysis");
    let root_path = Arc::new(root_path);

    let acc_path = matches.value_of("INPUT").unwrap();
    let server_path = matches.value_of("SERVER_LIST").unwrap();
    let (work_stack, acc_len) = parse_account_list(acc_path);
    let server_list = parse_server_list(server_path);
    let server_len = server_list.len();
    let timeout = if let Some(b) = matches.value_of("timeout") {
        b.parse().expect("Incorrect timeout supplied!")
    } else {
        0
    };

    let scheduler = Arc::new(Scheduler::with_worker_count(server_list, timeout));
    let counter = Arc::new(AtomicUsize::new(1));
    
    let mut f = File::create(format!("{}/analysis.csv", root_path)).expect("Could not create csv file!");
    f.write_all("address, steal ether, trigger suicide, hijack control flow\n".as_bytes()).expect("Could not write header to cvs!");
    let csv_writer = Arc::new(Mutex::new(BufWriter::new(f)));

    info!("Starting Analysis");
    let mut threads = Vec::new();
    for _ in 0..server_len {
        let work_stack_clone = Arc::clone(&work_stack);
        let scheduler_clone = Arc::clone(&scheduler);
        let counter_clone = Arc::clone(&counter);
        let root_path_clone = Arc::clone(&root_path);
        let csv_clone = Arc::clone(&csv_writer);
        let json = matches.is_present("json");
        let join_handle = thread::spawn(move || {
            execute(
                work_stack_clone,
                scheduler_clone,
                counter_clone,
                acc_len,
                root_path_clone,
                &csv_clone,
                json,
            )
        });
        threads.push(join_handle);
    }
    csv_writer.lock().unwrap().flush().expect("Could not finally flush writer");

    for handle in threads {
        let _res = handle.join();
    }
    info!("Finished Analysis");
}
