extern crate chrono;
extern crate clap;
extern crate esvm;
#[macro_use]
extern crate log;
extern crate fern;
extern crate num_cpus;
extern crate parity_connector;
extern crate yaml_rust;

#[macro_use]
extern crate serde_json;

use std::env;
use std::fs::{self, File};
use std::io::Read;

use chrono::prelude::*;
use clap::{App, Arg, ArgMatches};
use yaml_rust::YamlLoader;

use esvm::{symbolic_analysis, Attack, AttackType, SeEnviroment, Solvers, CONFIG};

fn init_logger(json_mode: bool) -> Result<(), fern::InitError> {
    let level = match env::var_os("RUST_LOG") {
        Some(level) => match level.to_str().unwrap() {
            "info" => log::LevelFilter::Info,
            "debug" => log::LevelFilter::Debug,
            "trace" => log::LevelFilter::Trace,
            _ => panic!("Declared invalid logging level!"),
        },
        None => log::LevelFilter::Info,
    };
    let mut builder = fern::Dispatch::new()
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
        .level(level)
        // allways log to log file
        .chain(fern::log_file("log/evmse.log")?);
    if !json_mode {
        builder = builder.chain(std::io::stdout());
    }

    builder.apply()?;
    Ok(())
}

pub fn main() {
    // init logger
    let matches = parse_args();
    init_logger(matches.is_present("json")).expect("Could not initialize logger");
    analysis(matches);
}

fn analysis(matches: ArgMatches) {
    // block people from being dumb
    assert!(
        !(matches.is_present("all_optimizations") && matches.is_present("disable_optimizations"))
    );

    esvm::set_global_config(&matches);
    if matches.is_present("list") {
        list_analysis(matches);
    } else {
        single_analysis(matches);
    }
}

fn list_analysis(matches: clap::ArgMatches) {
    {
        let g_config = CONFIG.read().unwrap();
        if g_config.parity.is_none() {
            panic!("On chain analysis must be run in conjunction with a parity node");
        }
    }
    let input = matches.value_of("INPUT").unwrap();
    let accounts = parse_input_list(input);

    let mut results = vec![];

    for (i, acc) in accounts.iter().enumerate() {
        info!("=========================================================");
        info!("Analyzing account {} of {}", i + 1, accounts.len());
        info!("=========================================================");
        if let Some(se_env) = SeEnviroment::from_chain(&acc) {
            let config = CONFIG.read().unwrap().clone();

            let pool = if let Some(solver) = matches.value_of("solver") {
                match solver {
                    "z3" => Solvers::Z3 {
                        count: CONFIG.read().unwrap().cores,
                        timeout: CONFIG.read().unwrap().solver_timeout,
                    },
                    "boolector" => Solvers::Boolector {
                        count: CONFIG.read().unwrap().cores,
                        timeout: CONFIG.read().unwrap().solver_timeout,
                    },
                    "yice" => Solvers::Yice {
                        count: CONFIG.read().unwrap().cores,
                        timeout: CONFIG.read().unwrap().solver_timeout,
                    },
                    _ => panic!("Supplied incorrect solver name"),
                }
            } else {
                Solvers::Yice {
                    count: CONFIG.read().unwrap().cores,
                    timeout: CONFIG.read().unwrap().solver_timeout,
                }
            };
            let ana_res = symbolic_analysis(se_env, config, pool);

            info!("=========================================================");
            for l in format!("{}", ana_res).lines() {
                info!("{}", l);
            }
            info!("=========================================================\n\n\n");
            results.push((acc.clone(), ana_res.attacks));
        } else {
            info!("=========================================================");
            info!(
                "Could not create env for {} (account selfdestructed?).",
                acc
            );
            info!("=========================================================");
        }
    }
    dump_result(results)
}

fn dump_result(results: Vec<(String, Option<Vec<Attack>>)>) {
    let mut content = String::new();

    // preamble
    content.push_str("address, steal ether, trigger suicide, hijack control flow\n");

    for (acc, attacks) in &results {
        let mut res = (false, false, false);
        if let Some(attacks) = attacks {
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
        content.push_str(&format!("{}, {}, {}, {}\n", acc, res.0, res.1, res.2));
    }

    let dt = Local::now();
    let file_name = dt.format("%Y-%m-%d-%H:%M:%S").to_string();
    fs::write(
        &format!("output/scan/{}-{}.csv", results.len(), file_name),
        &content,
    )
    .expect("Could not dump analysis results");
}

// assumes hex encoded ethereum addresses
fn parse_input_list(path: &str) -> Vec<String> {
    let mut f = File::open(path).unwrap();
    let mut s = String::new();
    f.read_to_string(&mut s).unwrap();
    s.lines()
        .map(|s| s.trim().trim_matches('\n').to_string())
        .collect()
}

fn single_analysis(matches: clap::ArgMatches) {
    let se_env;
    let input = matches.value_of("INPUT").unwrap();
    if matches.is_present("account") {
        {
            let g_config = CONFIG.read().unwrap();
            if g_config.parity.is_none() {
                panic!("On chain analysis must be run in conjunction with a parity node");
            }
            if let Some(env) = SeEnviroment::from_chain(input) {
                se_env = env;
            } else {
                info!("=========================================================");
                info!(
                    "Could not create env for {} (account selfdestructed?).",
                    input
                );
                info!("=========================================================");
                return;
            }
        }
    } else {
        let mut f = File::open(input).unwrap();
        let mut s = String::new();
        f.read_to_string(&mut s).unwrap();
        let yaml = YamlLoader::load_from_str(&s).unwrap();
        se_env = SeEnviroment::from_yaml(&yaml[0]);
    }

    let config = CONFIG.read().unwrap().clone();

    let pool = if let Some(solver) = matches.value_of("solver") {
        match solver {
            "z3" => Solvers::Z3 {
                count: CONFIG.read().unwrap().cores,
                timeout: CONFIG.read().unwrap().solver_timeout,
            },
            "boolector" => Solvers::Boolector {
                count: CONFIG.read().unwrap().cores,
                timeout: CONFIG.read().unwrap().solver_timeout,
            },
            "yice" => Solvers::Yice {
                count: CONFIG.read().unwrap().cores,
                timeout: CONFIG.read().unwrap().solver_timeout,
            },
            _ => panic!("Supplied incorrect solver name"),
        }
    } else {
        Solvers::Yice {
            count: CONFIG.read().unwrap().cores,
            timeout: CONFIG.read().unwrap().solver_timeout,
        }
    };

    let res = symbolic_analysis(se_env, config, pool);
    if matches.is_present("json") {
        println!("{}", json!(res));
    } else {
        for l in format!("{}", res).lines() {
            info!("{}", l);
        }
    }
}

fn parse_args<'a>() -> ArgMatches<'a> {
    let app = App::new("EthBMC")
        .version("1.0.0")
        .about("EthBMC: A Bounded Model Checker for Smart Contracts")
        // General
        .arg(
            Arg::with_name("INPUT")
                .help("Set input file / address")
                .required(true)
                .index(1),
        )
        .arg(Arg::with_name("json").long("json").help("Output json without logging"))
        .arg(Arg::with_name("account").long("acc").short("x").help("The input is an Ethereum account address, must be used with parity backend, mainnet only"))
        .arg(Arg::with_name("solver").long("solver").takes_value(true).help("The SMT solver to use: z3, boolector, yices2 [yices2]"))
        .arg(Arg::with_name("list").long("list").help("The input is a list of Ethereum account address, writes the result to a csv file in the output folder"));
    let app = esvm::arguments(app);
    app.get_matches()
}
