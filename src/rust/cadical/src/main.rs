// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};
use cadical_sys::{CaDiCal, Status};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    let mut positional = Vec::new();
    let mut quiet = false;
    let mut shrink = 0;
    let mut binary = true;
    let mut lrat = false;

    for arg in args.iter().skip(1) {
        if arg.starts_with("--") {
            if arg == "--quiet" {
                quiet = true;
            } else if arg.starts_with("--shrink=") {
                if let Ok(val) = arg["--shrink=".len()..].parse::<i32>() {
                    shrink = val;
                }
            } else if arg.starts_with("--binary=") {
                if let Ok(val) = arg["--binary=".len()..].parse::<bool>() {
                    binary = val;
                }
            } else if arg == "--lrat" {
                lrat = true;
            } else {
                // Ignore other options like --sat, --unsat, --default
            }
        } else {
            positional.push(arg);
        }
    }

    if positional.is_empty() {
        eprintln!("Usage: cadical <input-file> [ <proof-file> ] [options]");
        std::process::exit(1);
    }

    let input_file = &positional[0];
    let proof_file = if positional.len() > 1 {
        Some(&positional[1])
    } else {
        None
    };

    let mut solver = CaDiCal::new();

    if quiet {
        solver.set("quiet".to_string(), 1);
    }
    if shrink != 0 {
        solver.set("shrink".to_string(), shrink);
    }
    if lrat {
        solver.set("lrat".to_string(), 1);
    }
    if !binary {
        solver.set("binary".to_string(), 0);
    }

    if let Some(proof_path) = proof_file {
        if !solver.trace_proof2(proof_path.to_string()) {
            eprintln!("Failed to open proof file: {}", proof_path);
            std::process::exit(1);
        }
    }

    // Parse input CNF and track max variable index
    let mut max_var = 0;
    let file = File::open(input_file)?;
    let reader = BufReader::new(file);

    for line_result in reader.lines() {
        let line = line_result?;
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') || trimmed.starts_with('p') {
            continue;
        }
        for token in trimmed.split_whitespace() {
            if let Ok(lit) = token.parse::<i32>() {
                solver.add(lit);
                let var = lit.abs();
                if var > max_var {
                    max_var = var;
                }
            }
        }
    }

    // Solve
    let res = solver.solve();

    if res == Status::SATISFIABLE {
        println!("s SATISFIABLE");
        // Print assignment in DIMACS format: v 1 -2 3 ... 0
        print!("v");
        for var in 1..=max_var {
            let val = solver.val(var);
            if val > 0 {
                print!(" {}", var);
            } else if val < 0 {
                print!(" -{}", var);
            } else {
                print!(" {}", var);
            }
        }
        println!(" 0");
    } else if res == Status::UNSATISFIABLE {
        println!("s UNSATISFIABLE");
    } else {
        println!("s UNKNOWN");
    }

    // Flush and close proof tracing if enabled
    if proof_file.is_some() {
        solver.flush_proof_trace(true);
        solver.close_proof_trace(true);
    }

    Ok(())
}
