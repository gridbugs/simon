extern crate arg_combinators;

use arg_combinators::*;

fn main() {
    match opt::<f32>("", "width", "", "")
        .depend(opt::<f32>("", "height", "", ""))
        .option_map(|(x, y)| (x, y))
        .option_map(|(x, y)| x * y)
        .required()
        .just_parse_env_default()
    {
        Ok(area) => println!("area: {:?}", area),
        Err(e) => panic!("{}", e),
    }
}
