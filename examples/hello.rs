#![type_length_limit = "2097152"]
extern crate arg_combinators;

use arg_combinators::*;

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
