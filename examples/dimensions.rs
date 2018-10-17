extern crate simon;

use simon::*;

#[derive(Debug, Clone)]
enum Dimensions {
    Fullscreen,
    Window { width: u32, height: u32 },
}

impl Dimensions {
    fn args() -> ArgExt<impl Arg<Item = Self>> {
        let window =
            args_all_depend! {
                opt("", "width", "", ""),
                opt("", "height", "", ""),
            }.option_map(|(width, height)| Dimensions::Window { width, height });
        let fullscreen = flag("", "fullscreen", "").some_if(Dimensions::Fullscreen);
        window.either(fullscreen).required()
    }
}

fn main() {
    match Dimensions::args().with_help_default().parse_env_default() {
        (Ok(HelpOr::Value(dimensions)), _) => println!("{:#?}", dimensions),
        (Ok(HelpOr::Help), usage) => println!("{}", usage.render()),
        (Err(error), usage) => {
            print!("{}\n\n", error);
            print!("{}", usage.render());
            ::std::process::exit(1);
        }
    }
}
