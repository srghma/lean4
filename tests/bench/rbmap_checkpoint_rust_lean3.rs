use std::collections::BTreeMap;
use std::env;

type Map = BTreeMap<u64, bool>;

fn mk_map(mut n: u64, freq: u64) -> Vec<Map> {
    let mut stack = Vec::new();
    let mut map = Map::new();
    while n > 0 {
        n -= 1;
        map.insert(n, n % 10 == 0);
        if n % freq == 0 {
            stack.push(map.clone());
        }
    }
    stack.push(map);
    stack
}

fn fold(map: &Map) -> u64 {
    map.values().filter(|v| **v).count() as u64
}

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 3 {
        println!("invalid number of arguments");
        std::process::exit(1);
    }
    let n = args[1].parse().unwrap();
    let freq = args[2].parse().unwrap();
    let maps = mk_map(n, freq);
    println!("{}", fold(maps.last().unwrap()));
}
