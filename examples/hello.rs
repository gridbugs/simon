extern crate simon;

use simon::*;

fn main() {
    match free_str()
        .map(|v| v.get(0).cloned())
        .required()
        .just_parse_env_default()
    {
        Ok(name) => println!("Hello, {}!", name),
        Err(msg) => eprintln!("Error: {}", msg),
    }
}
