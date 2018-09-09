#![type_length_limit = "20097152"]
extern crate getopts;

pub mod arg;
pub mod ext;
pub mod util;
pub mod validation;

use arg::*;
pub use arg::Arg;
use ext::*;
pub use ext::ArgExt;
pub use ext::HelpOr;
use std::fmt::{Debug, Display};
use std::str::FromStr;

pub fn free_str() -> ArgExt<impl Arg<Item = Vec<String>>> {
    ext(Free)
}

pub fn free_by<F, T, E>(f: F) -> ArgExt<impl Arg<Item = Vec<T>>>
where
    F: Fn(String) -> Result<T, E>,
    E: Clone + Debug + Display,
{
    free_str().vec_convert(f)
}

pub fn free<T>() -> ArgExt<impl Arg<Item = Vec<T>>>
where
    T: FromStr + Debug + Display,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    free_by(|s| s.parse())
}

pub fn flag(short: &str, long: &str, doc: &str) -> ArgExt<impl Arg<Item = bool>> {
    ext(Flag::new(short, long, doc))
}

pub fn multiflag(short: &str, long: &str, doc: &str) -> ArgExt<impl Arg<Item = usize>> {
    ext(MultiFlag::new(short, long, doc))
}

pub fn opt_str(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> ArgExt<impl Arg<Item = Option<String>>> {
    ext(Opt::new(short, long, doc, hint))
}

pub fn opt_by<F, T, E>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    f: F,
) -> ArgExt<impl Arg<Item = Option<T>>>
where
    F: Fn(String) -> Result<T, E>,
    E: Clone + Debug + Display,
{
    opt_str(short, long, doc, hint).option_convert(f)
}

pub fn opt_by_default<F, T, E>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    default: T,
    f: F,
) -> ArgExt<impl Arg<Item = T>>
where
    F: Fn(String) -> Result<T, E>,
    E: Clone + Debug + Display,
    T: Clone + Display,
{
    opt_str(
        short,
        long,
        format!("{} (default: {})", doc, default).as_str(),
        hint,
    ).option_convert(f)
        .with_default(default)
}

pub fn opt_by_default_str<F, T, E>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    default: &str,
    f: F,
) -> ArgExt<impl Arg<Item = T>>
where
    F: Fn(String) -> Result<T, E>,
    E: Clone + Debug + Display,
{
    opt_str(
        short,
        long,
        format!("{} (default: {})", doc, default).as_str(),
        hint,
    ).with_default(default.to_string())
        .convert(f)
}

pub fn opt_by_required<F, T, E>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    f: F,
) -> ArgExt<impl Arg<Item = T>>
where
    F: Fn(String) -> Result<T, E>,
    E: Clone + Debug + Display,
    T: Display,
{
    opt_str(short, long, doc, hint).option_convert(f).required()
}

pub fn opt<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> ArgExt<impl Arg<Item = Option<T>>>
where
    T: FromStr + Debug + Display,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    opt_by(short, long, doc, hint, |s| s.parse())
}

pub fn opt_default<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    default: T,
) -> ArgExt<impl Arg<Item = T>>
where
    T: Clone + FromStr + Debug + Display,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    opt_str(
        short,
        long,
        format!("{} (default: {})", doc, default).as_str(),
        hint,
    ).option_convert(|s| s.parse())
        .with_default(default)
}

pub fn opt_default_str<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    default: &str,
) -> ArgExt<impl Arg<Item = T>>
where
    T: FromStr,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    opt_str(
        short,
        long,
        format!("{} (default: {})", doc, default).as_str(),
        hint,
    ).with_default(default.to_string())
        .convert(|s| s.parse())
}

pub fn opt_required<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> ArgExt<impl Arg<Item = T>>
where
    T: FromStr + Debug + Display,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    opt_str(short, long, doc, hint)
        .option_convert(|s| s.parse())
        .required()
}

pub fn multi_opt_str(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> ArgExt<impl Arg<Item = Vec<String>>> {
    ext(MultiOpt::new(short, long, doc, hint))
}

pub fn multi_opt_by<F, T, E>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    f: F,
) -> ArgExt<impl Arg<Item = Vec<T>>>
where
    F: Fn(String) -> Result<T, E>,
    E: Clone + Debug + Display,
{
    multi_opt_str(short, long, doc, hint).vec_convert(f)
}

pub fn multi_opt<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> ArgExt<impl Arg<Item = Vec<T>>>
where
    T: FromStr + Debug + Display,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    multi_opt_by(short, long, doc, hint, |s| s.parse())
}

pub fn value<T>(name: &str, value: T) -> ArgExt<impl Arg<Item = T>>
where
    T: Clone,
{
    ext(Value::new(name, value))
}

#[macro_export]
macro_rules! unflatten_closure {
    ( $p:pat => $tup:expr ) => {
        |$p| $tup
    };
    ( $p:pat => ( $($tup:tt)* ), $head:expr $(, $tail:expr)* ) => {
        unflatten_closure!( ($p, a) => ( $($tup)*, a) $(, $tail )* )
    };
}

#[macro_export]
macro_rules! args_all {
    ( $only:expr ) => {
        $only
    };
    ( $head:expr, $($tail:expr),* $(,)* ) => {
        $head $( .both($tail) )*
            .map(
                unflatten_closure!(a => (a) $(, $tail )*)
            )
    };
}

#[macro_export]
macro_rules! args_all_depend {
    ( $only:expr ) => {
        $only
    };
    ( $head:expr, $($tail:expr),* $(,)* ) => {
        $head $( .depend($tail) )*
            .option_map(
                unflatten_closure!(a => (a) $(, $tail )*)
            )
    };
}

#[macro_export]
macro_rules! args_map {
    ( let { $var1:ident = $a1:expr; } in { $b:expr } ) => {
        $a1.map(|$var1| $b)
    };
    ( let { $var1:ident = $a1:expr; $($var:ident = $a:expr;)+ } in { $b:expr } ) => {
        { args_all! {
            $a1, $($a),*
        } } .map(|($var1, $($var),*)| $b)
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn basic() {
        assert_eq!(
            opt_required::<u32>("f", "foo", "", "")
                .just_parse(&["--foo", "42"])
                .unwrap(),
            42
        );
    }

    #[test]
    fn basic_macros() {
        assert_eq!(
            args_map! {
                let {
                    a = opt_required::<u32>("f", "foo", "", "");
                    b = opt_required::<u32>("b", "bar", "", "");
                } in {
                    a + b
                }
            }.just_parse(&["--foo", "7", "--bar", "9"])
                .unwrap(),
            16
        );
    }

    #[test]
    fn args_all_depend() {
        assert_eq!(
            args_all_depend! {
                opt::<u32>("f", "foo", "", ""),
                opt::<u32>("b", "bar", "", ""),
            }.required()
                .map(|(a, b)| a + b)
                .just_parse(&["--foo", "7", "--bar", "9"])
                .unwrap(),
            16
        );
    }

    #[test]
    fn validation() {
        let no_args: &[&'static str] = &[];
        let has_empty_switch = args_all! {
            opt_str("", "", "doc", "hint"),
            opt_str("c", "control", "", ""),
        }.valid();
        let duplicate_switches = args_all! {
            opt_str("a", "aa", "", ""),
            opt_str("b", "aa", "", ""),
            opt_str("a", "bb", "", ""),
            opt_str("c", "control", "", ""),
        }.valid();
        let invalid_switches = args_all! {
            opt_str("aa", "", "", ""),
            opt_str("", "a", "", ""),
            opt_str("a", "b", "", ""),
            opt_str("bb", "aa", "", ""),
            opt_str("c", "control", "", ""),
        }.valid();

        match has_empty_switch.just_parse(no_args).unwrap_err() {
            TopLevelError::Other(ValidError::Invalid(invalid)) => {
                assert_eq!(
                    invalid,
                    validation::Invalid {
                        has_empty_switch: true,
                        ..Default::default()
                    }
                );
            }
            other => panic!("{:?}", other),
        }

        match duplicate_switches.just_parse(no_args).unwrap_err() {
            TopLevelError::Other(ValidError::Invalid(invalid)) => {
                assert_eq!(
                    invalid,
                    validation::Invalid {
                        duplicate_shorts: vec!["a".to_string()],
                        duplicate_longs: vec!["aa".to_string()],
                        ..Default::default()
                    }
                );
            }
            other => panic!("{:?}", other),
        }

        match invalid_switches.just_parse(no_args).unwrap_err() {
            TopLevelError::Other(ValidError::Invalid(invalid)) => {
                assert_eq!(
                    invalid,
                    validation::Invalid {
                        one_char_longs: vec!["a".to_string(), "b".to_string()],
                        multi_char_shorts: vec!["aa".to_string(), "bb".to_string()],
                        ..Default::default()
                    }
                );
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn deep_recursion() {
        let _ = value("", Some(42))
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x)
            .option_map(|x| x);

        let _ = value("", vec![1, 2, 3])
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1)
            .vec_map(|x| x + 1);

        let _ = args_all! {
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
            value("", 1),
        };

        let _ = args_all_depend! {
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
            value("", Some(1)),
        };
    }
}
