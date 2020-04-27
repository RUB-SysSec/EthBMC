#![feature(proc_macro_hygiene, decl_macro)]

#[macro_use]
extern crate log;

extern crate chrono;
extern crate clap;
extern crate esvm;
extern crate ethereum_newtypes;
extern crate fern;
extern crate num_cpus;
#[macro_use]
extern crate rocket;
extern crate subprocess;

use std::{env, io::Read};

use clap::{App, ArgMatches};
use esvm::{
    symbolic_analysis, AnalysisResult, AnalysisSuccess, SeEnviroment, Solvers, TimeoutAnalysis,
    CONFIG,
};
use ethereum_newtypes::Address;
use rocket_contrib::json::Json;
use subprocess::{Exec, Redirection};

static SOLVER_TIMEOUT: usize = 120_000;

fn init_logger() -> Result<(), fern::InitError> {
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
        .chain(fern::log_file("log/evmse-service.log")?)
        // Apply globally
        .apply()?;
    Ok(())
}

fn build_args(message: &Json<TimeoutAnalysis>) -> Vec<String> {
    let mut args = vec![
        "-x".to_string(),
        format!("{:x}", message.0.address),
        "--json".to_string(),
    ];

    let mut cli_args = env::args();
    cli_args.next(); // remove silly path
    args.append(&mut cli_args.collect());
    args
}

#[post(
    "/analyze_address_timeout",
    format = "application/json",
    data = "<message>"
)]
fn analyze_address_timeout(message: Json<TimeoutAnalysis>) -> Json<AnalysisSuccess> {
    let args = build_args(&message);

    let mut process = match Exec::cmd("ethaeg")
        .args(&args)
        .stderr(Redirection::Merge) // redirect err output to stdout
        .stdout(Redirection::Pipe)
        .popen()
    {
        Err(why) => panic!("couldn't spawn ethaeg: {}", why),
        Ok(process) => process,
    };

    match process.wait_timeout(message.0.timeout) {
        Ok(result) => {
            process.kill().unwrap();
            if let None = result {
                info!("Analysis for {:x} timed out!", message.0.address);
                return Json(AnalysisSuccess::Timeout);
            }
        }
        Err(error) => {
            return Json(AnalysisSuccess::Failure(format!(
                "Error waiting for subprocess: {}",
                error
            )));
        }
    };

    let mut buffer = String::new();
    // we go now
    if let Err(_) = process.stdout.take().unwrap().read_to_string(&mut buffer) {
        return Json(AnalysisSuccess::Failure(
            "Could not capture ethaeg output".to_string(),
        ));
    }

    match serde_json::from_str(&buffer) {
        Ok(succ) => Json(AnalysisSuccess::Success(succ)),
        Err(error) => Json(AnalysisSuccess::Failure(format!(
            "Could not parse ethaeg output:\n{}\n{}",
            buffer, error
        ))),
    }
}

#[post("/analyze_address", format = "application/json", data = "<message>")]
fn analyze_address(message: Json<Address>) -> Json<AnalysisSuccess> {
    let solver = Solvers::Yice {
        count: CONFIG.read().unwrap().cores,
        timeout: SOLVER_TIMEOUT,
    };
    let result = analyze(solver, message.0);
    match result {
        Some(succ) => Json(AnalysisSuccess::Success(succ)),
        None => Json(AnalysisSuccess::Failure(
            "Could not create environment for analysis!".to_string(),
        )),
    }
}

#[get("/alive")]
fn alive() -> &'static str {
    "staying alive"
}

fn analyze(pool: Solvers, addr: Address) -> Option<AnalysisResult> {
    info!("Analyzing address: {:x}", addr.0);
    let se_env = SeEnviroment::from_chain(&format!("{:x}", addr.0))?;
    let config = CONFIG.read().unwrap().clone();
    Some(symbolic_analysis(se_env, config, pool))
}

fn rocket() -> rocket::Rocket {
    rocket::ignite().mount(
        "/analyses",
        routes![analyze_address, analyze_address_timeout, alive],
    )
}

fn parse_args<'a>() -> ArgMatches<'a> {
    let app = App::new("EthAEG webservice");
    let app = esvm::arguments(app);
    app.get_matches()
}

fn main() {
    init_logger().expect("Could not initialize logger");
    let matches = parse_args();
    esvm::set_global_config(&matches);
    rocket().launch();
}
