use simon::*;

fn main() {
    match opt::<f32>("", "width", "", "")
        .depend(opt::<f32>("", "height", "", ""))
        .option_map(|(x, y)| (x, y))
        .option_map(|(x, y)| x * y)
        .required()
        .parse_env()
        .result
    {
        Ok(area) => println!("area: {:?}", area),
        Err(e) => panic!("{}", e),
    }
}
