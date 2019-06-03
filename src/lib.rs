//! # Simon (an Arg Functor)
//!
//! A library for declaratively specifying and parsing command-line arguments.
//!
//! # Toy Example
//!
//! ```rust
//! extern crate simon;
//!
//! let (name, age): (String, u8) =
//!     simon::opt_required("n", "name", "your name", "NAME")
//!        .both(
//!           simon::opt("a", "age", "your age", "NUM")
//!              .with_default(42)
//!        )
//!        .just_parse(&["--name", "Stephen", "-a", "26"])
//!        .expect("Invalid command line argument");
//!
//! assert_eq!(name, "Stephen");
//! assert_eq!(age, 26);
//! ```
//!
//! # Usage
//!
//! Typical usage is to define a type to contain your command-line arguments
//! (typically tuple or struct where each field corresponds to an argument), and
//! then construct, from a library of combinators, a parser which knows how to
//! parse a value of this type from command line arguments.
//!
//! At the core of this library is the [Arg] trait. Implementations of [Arg]
//! know how to parse a value of a particular type ([Arg]'s associated type
//! `Item`) out of command line arguments. This might be as simple as taking a
//! string value directly from the command line arguments. More complicated
//! [Arg] implementations combine multiple simpler [Arg]s together, or
//! manipulate their output in some way. I'll sometimes refer to implementations
//! of [Arg] where `type Item = Foo` as "parsers yielding a value of type
//! `Foo`".
//!
//! The `ArgExt` struct is a wrapper around [Arg] implementations, adding
//! methods which can be chained to create more complex parsers.
//!
//! This library provides "base" parsers, which parse individual command-line
//! arguments, and "combinators" - methods of `ArgExt` which modify or combine
//! simpler parsers. Base parsers for arguments which accept parameters have
//! variants which yield values of inferred types, converted using [FromStr],
//! and additional variants which yield values converted from strings by a
//! provided conversion function.
//! There are also a handful of macros for ergonomics, and
//! simplifying some common patterns.
//!
//! In the example above, `opt_required` and `opt` are both parsers yielding
//! values of inferred types (in this case [String] and [u8]), while
//! `both` and `with_default` are combinators. The `both` combinators takes a
//! pair of parsers, and creates a parser yielding the pair containing both
//! parsers' outputs. The `with_default` combinator takes a parser which yields
//! an optional value, and a value, and returns a parser which yields the
//! provided value if a value was provided, and the default value otherwise.
//!
//! # Argument Types
//!
//! This library recognises 5 types of command line argument:
//!
//!  - a **flag** is a named argument with no parameter which may appear 0 or 1
//!  times. Base parsers of flags yield `bool` values which are `true` when an
//!  argument appears once, and `false` otherwise.
//!  - a **multi_flag** is a named argument with no parameter which may appear an
//!  arbitrary number of times. Base parsers of multi_flags yield `usize` values
//!  equal to the number of times the argument was passed.
//!  - an **opt** is a named argument with a parameter, which may appear 0 or 1 times.
//!  Base parsers of opts yield `Option<String>` values which are `Some(<value>)`
//!  if the argument was passed, and `None` otherwise.
//!  - a **multi_opt** is a named argument with a value which may appear an
//!  arbitrary number of times. The argument name must appear before each value.
//!  Base parsers of multi_opts yield `Vec<String>`
//!  values, with an element for each value that was passed.
//!  - a **free** is an unnamed argument. An arbitrary number of frees may be
//!  passed. Base parsers of frees yield 'Vec<String>` values, with an element
//!  for each value that was passed.
//!
//! # Errors
//!
//! ## Parse Errors
//!
//! Parse errors are the result of invalid command-line arguments being passed
//! to a program.
//! In addition to the `Item` associated type, the [Arg] trait has an additional
//! associated type named `Error`. Implementations of [Arg] can use this type to
//! return errors detected during parsing. Combinators typically propagate
//! errors of child parsers through their own `Error`s, though they are of
//! course free to handle these errors themselves. Some example parse errors:
//!
//! - missing required arguments
//! - parameters passed which can't be converted to the required type
//! - passing multiple mutually exclusive arguments
//!
//! ## Spec Errors
//!
//! Spec errors are problems with the specification of arguments themselves.
//! Some examples of spec errors:
//!
//! - specifying the same argument name multiple times
//! - specifying a short name longer than 1 character
//! - specifying a long name with a length of 1 character
//! - specifying neither a short name, nor a long name
//!
//! Since spec errors don't depend on the specific arguments passed to a
//! program, running a program once is usually enough to convince yourself that
//! it is free of these errors. As such, spec errors cause panics while parsing.
//!
//! If however, your program's arguments are
//! generated dynamically (such as from a config file or locale), you want a way
//! to handle spec errors. The combinator [ArgExt::valid] creates a parser
//! which treats spec errors as if they were parse errors - returning an error during
//! parsing rather than panicking.
//!
//! # Parsing real command-line arguments
//!
//! The [Toy Example](#toy-example) above specified the arguments in a slice. In practice, most
//! programs will read actual command-line arguments. Methods for running
//! a parser on real command-line arguments are [ArgExt::parse_env] and
//! [ArgExt::parse_env_or_exit], and their variants.
//!
//! # Help and Usage
//!
//! The combinator [ArgExt::with_help] creates a parser which accepts a help flag.
//! The [ArgExt::with_help_default] combinator is the same, but it uses the flag
//! "-h" and "--help".
//!
//! The [ArgExt::parse_env] function returns a [Usage] in addition to a parsed
//! value or error, which can be rendered ([Usage::render]) to produce
//! documentation on arguments, suitable for printing when help was requested,
//! or the user have invalid input.
//!
//! The methods [ArgExt::parse_env_or_exit] and
//! [ArgExt::parse_env_default_or_exit] are only available on values
//! produced by [ArgExt::with_help] and [ArgExt::with_help_default]
//! irrespectively. These functions run the parser on the program's command-line
//! arguments, and print usage and exit if a parser error was detected, or help
//! was requested, and returns the parsed value otherwise.
extern crate getopts;

pub mod arg;
pub mod ext;
pub mod util;
pub mod validation;

pub use arg::Arg;
use arg::*;
pub use ext::ArgExt;
pub use ext::HelpOr;
use ext::*;
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

pub fn multi_flag(short: &str, long: &str, doc: &str) -> ArgExt<impl Arg<Item = usize>> {
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
    )
    .option_convert(f)
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
    )
    .with_default(default.to_string())
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
    )
    .option_convert(|s| s.parse())
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
    )
    .with_default(default.to_string())
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

#[macro_export]
macro_rules! args_either {
    ( $only:expr ) => {
        $only
    };
    ( $head:expr, $($tail:expr),* $(,)* ) => {
        $head $( .either($tail) )*
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
            }
            .just_parse(&["--foo", "7", "--bar", "9"])
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
            }
            .required()
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
        }
        .valid();
        let duplicate_switches = args_all! {
            opt_str("a", "aa", "", ""),
            opt_str("b", "aa", "", ""),
            opt_str("a", "bb", "", ""),
            opt_str("c", "control", "", ""),
        }
        .valid();
        let invalid_switches = args_all! {
            opt_str("aa", "", "", ""),
            opt_str("", "a", "", ""),
            opt_str("a", "b", "", ""),
            opt_str("bb", "aa", "", ""),
            opt_str("c", "control", "", ""),
        }
        .valid();

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
    fn either() {
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum E {
            A,
            B,
            C(String),
        }

        let choice = args_either! {
            flag("a", "", "").some_if(E::A),
            flag("b", "", "").some_if(E::B),
            opt("c", "", "", "").option_map(|s| E::C(s)),
        }
        .required()
        .just_parse(&["-c", "foo"])
        .unwrap();

        assert_eq!(choice, E::C("foo".to_string()));
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
