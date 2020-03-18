use simon::*;

fn main() {
    match free::<String>()
        .vec_singleton()
        .required()
        .parse_env()
        .result
    {
        Ok(name) => println!("Hello, {}!", name),
        Err(msg) => eprintln!("Error: {}", msg),
    }
}
