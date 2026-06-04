use std::collections::BTreeMap;
use std::env;

type Map = BTreeMap<u64, bool>;

fn mk_map(mut n: u64) -> Map {
    let mut map = Map::new();
    while n > 0 {
        n -= 1;
        map.insert(n, n % 10 == 0);
    }
    map
}

fn fold(map: &Map) -> u64 {
    map.values().filter(|v| **v).count() as u64
}

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("invalid number of arguments");
        std::process::exit(1);
    }
    let n = args[1].parse().unwrap();
    println!("{}", fold(&mk_map(n)));
}
