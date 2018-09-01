extern crate either;
extern crate getopts;

use std::str::FromStr;
use std::fmt::Display;

pub mod ext;
pub mod param;

pub use ext::{ParamExt, ParamOptExt};

use param::*;

pub fn arg_req<T: FromStr>(short: &str, long: &str, hint: &str, doc: &str) -> impl Param<Item = T> {
    ArgSpec::new_from_str_required(short, long, hint, doc)
}

pub fn arg_opt<T: FromStr>(
    short: &str,
    long: &str,
    hint: &str,
    doc: &str,
) -> impl Param<Item = Option<T>> {
    ArgSpec::new_from_str_optional(short, long, hint, doc)
}

pub fn arg_opt_def<T: FromStr + Display + Clone>(
    short: &str,
    long: &str,
    hint: &str,
    doc: &str,
    default: T,
) -> impl Param<Item = T> {
    let doc = doc.to_string();
    ArgSpec::new_from_str_optional_with_default(
        short,
        long,
        hint,
        move |x| format!("{} {}", doc, x),
        default,
    )
}

fn example() {
    let arg_spec = ArgSpec {
        short: "f".to_string(),
        long: "foo".to_string(),
        hint: "value".to_string(),
        doc: optional_with_default_doc_debug("a number"),
        occur: optional_with_default(42),
        convert: default_convert,
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn example1() {
        let p = arg_req::<i32>("int")
            .map(|i| i + 1)
            .join(arg_req::<f32>("float"));
        let (i, f) = p.parse(&["--float", "6.5", "--int", "42"]).unwrap();
        assert_eq!(i, 43);
        assert_eq!(f, 6.5);
    }
    #[derive(Debug, PartialEq, Eq)]
    enum Size {
        Dimensions(i32, i32),
        Fullscreen,
    }
    #[test]
    fn example2() {
        let p_dimensions = arg_opt::<i32>("width")
            .opt_join(arg_opt::<i32>("height"))
            .opt_map(|(width, height)| Size::Dimensions(width, height));
        let p_fullscreen =
            flag("fullscreen").map(|f| if f { Some(Size::Fullscreen) } else { None });
        let p = p_dimensions.either_same_type(p_fullscreen).required();
        let s = p.parse(&["--width", "4", "--height", "5"]).unwrap();
        assert_eq!(s, Size::Dimensions(4, 5));
    }
}
