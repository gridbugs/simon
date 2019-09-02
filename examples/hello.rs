extern crate simon;

use simon::*;

fn main() {
    match free::<String>()
        .map(|v| v.into_iter().next())
        .required()
        .parse_env()
        .result
    {
        Ok(name) => println!("Hello, {}!", name),
        Err(msg) => eprintln!("Error: {}", msg),
    }
}
