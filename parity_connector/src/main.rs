extern crate clap;
extern crate parity_connector;
extern crate uint;

use clap::{App, Arg, ArgMatches};
use parity_connector::{create_client, BlockSelector};
use uint::U256;

fn main() {
    let matches = parse_args();

    let ip = matches.value_of("IP").unwrap();
    let port = matches
        .value_of("port")
        .unwrap_or("8545")
        .parse::<isize>()
        .unwrap();

    let mut client = create_client(ip, port);
    let result1 = client.blocknumber();
    let res2 = client.block_by_number(BlockSelector::Specific(4_649_480));
    let res3 = client.storage(
        U256::from_dec_str("121489304910085681030520874682045790491262858723").unwrap(),
        BlockSelector::Specific(4_649_480),
    );

    println!("{:?}", result1);
    println!("{:?}", res2);
    println!("{:?}", res2.difficulty());
    println!("{:?}", res3);

    let res = client.code(
        U256::from_dec_str("1130997971043064165214724645812216908397186898329").unwrap(),
        BlockSelector::Latest,
    );
    println!("{:?}", res);

    let res = client.storage(
        U256::from_dec_str("1130997971043064165214724645812216908397186898329").unwrap(),
        BlockSelector::Latest,
    );
    println!("{:?}", res);
}

fn parse_args<'a>() -> ArgMatches<'a> {
    App::new("Parity ClI")
        .version("0.1.0")
        .about("Simple Cli client for testing parity")
        .arg(
            Arg::with_name("IP")
                .required(true)
                .index(1)
                .help("Ip address of the running parity jsonrpc server"),
        )
        .arg(
            Arg::with_name("port")
                .short("p")
                .long("port")
                .help("port number standard: 8545")
                .takes_value(true),
        )
        .get_matches()
}
