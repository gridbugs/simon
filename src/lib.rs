extern crate getopts;

use std::env;
use std::ffi::OsStr;
use std::fmt;
use std::process;
use std::str::FromStr;

mod util;
mod validation;
pub use util::Never;
pub use validation::Invalid;

pub type Matches = getopts::Matches;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct SwitchCommon {
    pub short: String,
    pub long: String,
    pub doc: String,
}

impl SwitchCommon {
    fn new(short: &str, long: &str, doc: &str) -> Self {
        Self {
            short: short.to_string(),
            long: long.to_string(),
            doc: doc.to_string(),
        }
    }

    fn key_to_search_in_matches(&self) -> &str {
        if self.short.len() != 0 {
            self.short.as_str()
        } else {
            self.long.as_str()
        }
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum SwitchShape {
    Flag,
    Opt { hint: String },
}

pub trait Switches {
    fn add(&mut self, common: SwitchCommon, shape: SwitchShape);
}

impl Switches for getopts::Options {
    fn add(&mut self, common: SwitchCommon, shape: SwitchShape) {
        match shape {
            SwitchShape::Flag => {
                self.optflag(
                    common.short.as_str(),
                    common.long.as_str(),
                    common.doc.as_str(),
                );
            }
            SwitchShape::Opt { hint } => {
                self.optopt(
                    common.short.as_str(),
                    common.long.as_str(),
                    common.doc.as_str(),
                    hint.as_str(),
                );
            }
        }
    }
}

#[derive(Debug)]
pub enum TopLevelError<E> {
    Getopts(getopts::Fail),
    Other(E),
}

impl<E: fmt::Display> fmt::Display for TopLevelError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Getopts(fail) => fmt::Display::fmt(&fail, f),
            Self::Other(other) => fmt::Display::fmt(&other, f),
        }
    }
}

pub struct Usage {
    opts: getopts::Options,
    program_name: String,
}

impl Usage {
    pub fn render(&self) -> String {
        let brief = format!("Usage: {} [options]", &self.program_name);
        self.opts.usage(&brief)
    }
}

pub struct ParseResult<I, E> {
    pub usage: Usage,
    pub result: Result<I, TopLevelError<E>>,
}

pub trait Arg: Sized {
    type Item;
    type Error: fmt::Debug + fmt::Display;
    fn update_switches<S: Switches>(&self, switches: &mut S);
    fn name(&self) -> String;
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error>;
    fn validate(&self) -> Result<(), Invalid> {
        let mut checker = validation::Checker::default();
        self.update_switches(&mut checker);
        if let Some(invalid) = checker.invalid() {
            Err(invalid)
        } else {
            Ok(())
        }
    }
    fn parse_specified_ignoring_validation<I>(
        self,
        program_name: String,
        args: I,
    ) -> ParseResult<Self::Item, Self::Error>
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        let mut opts = getopts::Options::new();
        self.update_switches(&mut opts);
        ParseResult {
            result: opts
                .parse(args)
                .map_err(TopLevelError::Getopts)
                .and_then(|matches| self.get(&matches).map_err(TopLevelError::Other)),
            usage: Usage { opts, program_name },
        }
    }
    fn parse_specified<I>(
        self,
        program_name: String,
        args: I,
    ) -> ParseResult<Self::Item, Self::Error>
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        if let Err(invalid) = self.validate() {
            panic!("Invalid command spec:\n{}", invalid);
        }
        self.parse_specified_ignoring_validation(program_name, args)
    }
    fn parse_env(self) -> ParseResult<Self::Item, Self::Error> {
        let args = env::args().collect::<Vec<_>>();
        let program_name = args[0].clone();
        self.parse_specified(program_name, &args[1..])
    }
    fn with_help(self, help_flag: Flag) -> WithHelp<Self> {
        WithHelp {
            arg: self,
            help_flag,
        }
    }
    fn with_help_default(self) -> WithHelp<Self> {
        self.with_help(Flag::new("h", "help", "print this help menu"))
    }
    fn option_map<F, T, U>(self, f: F) -> OptionMap<Self, F>
    where
        F: FnOnce(T) -> U,
    {
        OptionMap { arg: self, f }
    }
    fn with_default<T>(self, default_value: T) -> WithDefault<Self, T> {
        WithDefault {
            arg: self,
            default_value,
        }
    }
    fn choice<O>(self, other: O) -> Choice<Self, O>
    where
        O: Arg<Item = Self::Item>,
    {
        Choice { a: self, b: other }
    }
    fn both<O>(self, other: O) -> Both<Self, O>
    where
        O: Arg,
    {
        Both { a: self, b: other }
    }
    fn map<F, U>(self, f: F) -> Map<Self, F>
    where
        F: FnOnce(Self::Item) -> U,
    {
        Map { arg: self, f }
    }
    fn required(self) -> Required<Self> {
        Required { arg: self }
    }
    fn option_convert_string<F, T, E>(self, f: F) -> OptionConvertString<Self, F>
    where
        F: FnOnce(&str) -> Result<T, E>,
    {
        OptionConvertString { arg: self, f }
    }
    fn vec_convert_string<F, T, E>(self, f: F) -> VecConvertString<Self, F>
    where
        F: FnMut(&str) -> Result<T, E>,
    {
        VecConvertString { arg: self, f }
    }
    fn depend<O>(self, other: O) -> Depend<Self, O>
    where
        O: Arg,
    {
        Depend { a: self, b: other }
    }
    fn some_if<T>(self, t: T) -> SomeIf<Self, T> {
        SomeIf { arg: self, t }
    }
}

pub struct Flag {
    common: SwitchCommon,
}

impl Flag {
    pub fn new(short: &str, long: &str, doc: &str) -> Self {
        Self {
            common: SwitchCommon::new(short, long, doc),
        }
    }
}
impl Arg for Flag {
    type Item = bool;
    type Error = Never;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        switches.add(self.common.clone(), SwitchShape::Flag);
    }
    fn name(&self) -> String {
        self.common.long.clone()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_present(self.common.key_to_search_in_matches()))
    }
}

pub struct Opt {
    common: SwitchCommon,
    hint: String,
}

impl Opt {
    pub fn new(short: &str, long: &str, doc: &str, hint: &str) -> Self {
        Self {
            common: SwitchCommon::new(short, long, doc),
            hint: hint.to_string(),
        }
    }
}

impl Arg for Opt {
    type Item = Option<String>;
    type Error = Never;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        switches.add(
            self.common.clone(),
            SwitchShape::Opt {
                hint: self.hint.clone(),
            },
        );
    }
    fn name(&self) -> String {
        self.common.long.clone()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_str(self.common.key_to_search_in_matches()))
    }
}

pub struct Free;

impl Arg for Free {
    type Item = Vec<String>;
    type Error = Never;
    fn update_switches<S: Switches>(&self, _switches: &mut S) {}
    fn name(&self) -> String {
        "ARGS".to_string()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.free.clone())
    }
}

pub struct WithHelp<A> {
    arg: A,
    help_flag: Flag,
}

pub enum OrHelp<T> {
    Value(T),
    Help,
}

impl<A> Arg for WithHelp<A>
where
    A: Arg,
{
    type Item = OrHelp<A::Item>;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
        self.help_flag.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("({}) with help", self.arg.name())
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        if Never::result_ok(self.help_flag.get(matches)) {
            Ok(OrHelp::Help)
        } else {
            self.arg.get(matches).map(OrHelp::Value)
        }
    }
}

impl<A> WithHelp<A>
where
    A: Arg,
{
    pub fn parse_env_or_exit(self) -> A::Item {
        let ParseResult { result, usage } = self.parse_env();
        match result {
            Ok(OrHelp::Value(a)) => a,
            Ok(OrHelp::Help) => {
                print!("{}", usage.render());
                process::exit(0);
            }
            Err(e) => {
                eprint!("{}\n\n", e);
                eprint!("{}", usage.render());
                process::exit(1);
            }
        }
    }
}

pub struct OptionMap<A, F>
where
    A: Arg,
{
    arg: A,
    f: F,
}

impl<A, F, T, U> Arg for OptionMap<A, F>
where
    A: Arg<Item = Option<T>>,
    F: FnOnce(T) -> U,
{
    type Item = Option<U>;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let Self { arg, f } = self;
        arg.get(matches).map(|x| x.map(f))
    }
}

pub struct WithDefault<A, T>
where
    A: Arg,
{
    arg: A,
    default_value: T,
}

impl<A, T> Arg for WithDefault<A, T>
where
    A: Arg<Item = Option<T>>,
{
    type Item = T;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let Self { arg, default_value } = self;
        arg.get(matches).map(|x| x.unwrap_or(default_value))
    }
}

pub struct Choice<A, B>
where
    A: Arg,
    B: Arg,
{
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum ChoiceError<A, B> {
    A(A),
    B(B),
    MultipleMutuallyExclusiveArgs { a: String, b: String },
}

impl<A, B> fmt::Display for ChoiceError<A, B>
where
    A: fmt::Display,
    B: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::A(a) => a.fmt(f),
            Self::B(b) => b.fmt(f),
            Self::MultipleMutuallyExclusiveArgs { a, b } => {
                write!(f, "({}) and ({}) are mutually exclusive", a, b)
            }
        }
    }
}

impl<A, B, T> Arg for Choice<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<T>>,
{
    type Item = Option<T>;
    type Error = ChoiceError<A::Error, B::Error>;

    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
        self.b.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("choose ({}) or ({})", self.a.name(), self.b.name())
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let Self { a, b } = self;
        let multiple_mutually_exclusive_args =
            ChoiceError::MultipleMutuallyExclusiveArgs {
                a: a.name(),
                b: b.name(),
            };

        if let Some(a_value) = a.get(matches).map_err(ChoiceError::A)? {
            if b.get(matches).map_err(ChoiceError::B)?.is_some() {
                Err(multiple_mutually_exclusive_args)
            } else {
                Ok(Some(a_value))
            }
        } else {
            b.get(matches).map_err(ChoiceError::B)
        }
    }
}

#[derive(Debug)]
pub enum BothError<A, B> {
    A(A),
    B(B),
}

impl<A, B> fmt::Display for BothError<A, B>
where
    A: fmt::Display,
    B: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::A(a) => a.fmt(f),
            Self::B(b) => b.fmt(f),
        }
    }
}

pub struct Both<A, B>
where
    A: Arg,
    B: Arg,
{
    a: A,
    b: B,
}

impl<A, B> Arg for Both<A, B>
where
    A: Arg,
    B: Arg,
{
    type Item = (A::Item, B::Item);
    type Error = BothError<A::Error, B::Error>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
        self.b.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok((
            self.a.get(matches).map_err(BothError::A)?,
            self.b.get(matches).map_err(BothError::B)?,
        ))
    }
}

pub struct Map<A, F>
where
    A: Arg,
{
    arg: A,
    f: F,
}
impl<A, U, F> Arg for Map<A, F>
where
    A: Arg,
    F: FnOnce(A::Item) -> U,
{
    type Item = U;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let Self { arg, f } = self;
        arg.get(matches).map(f)
    }
}

pub struct Value<T> {
    value: T,
    name: String,
}

impl<T> Value<T> {
    pub fn new(name: &str, value: T) -> Self {
        Self {
            name: name.to_string(),
            value,
        }
    }
}

impl<T> Arg for Value<T> {
    type Item = T;
    type Error = Never;
    fn update_switches<S: Switches>(&self, _switches: &mut S) {}
    fn name(&self) -> String {
        self.name.clone()
    }
    fn get(self, _matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.value)
    }
}

pub struct Required<A>
where
    A: Arg,
{
    arg: A,
}

#[derive(Debug)]
pub enum RequiredError<A> {
    Arg(A),
    MissingRequiredArg { name: String },
}

impl<A> fmt::Display for RequiredError<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Arg(a) => a.fmt(f),
            Self::MissingRequiredArg { name } => {
                write!(f, "missing required argument ({})", name)
            }
        }
    }
}

impl<A, T> Arg for Required<A>
where
    A: Arg<Item = Option<T>>,
{
    type Item = T;
    type Error = RequiredError<A::Error>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let name = self.arg.name();
        if let Some(x) = self.arg.get(matches).map_err(RequiredError::Arg)? {
            Ok(x)
        } else {
            Err(RequiredError::MissingRequiredArg { name })
        }
    }
}

pub struct OptionConvertString<A, F>
where
    A: Arg,
{
    arg: A,
    f: F,
}

#[derive(Debug)]
pub enum OptionConvertStringError<A, E> {
    Arg(A),
    FailedToConvert {
        name: String,
        arg_string: String,
        error: E,
    },
}

impl<A, E> fmt::Display for OptionConvertStringError<A, E>
where
    A: fmt::Display,
    E: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Arg(a) => a.fmt(f),
            Self::FailedToConvert {
                name,
                arg_string,
                error,
            } => write!(
                f,
                "failed to convert argument ({}). \"{}\" could not be parsed (error: {})",
                name, arg_string, error
            ),
        }
    }
}

impl<A, F, T, E> Arg for OptionConvertString<A, F>
where
    A: Arg<Item = Option<String>>,
    F: FnOnce(&str) -> Result<T, E>,
    E: fmt::Display + fmt::Debug,
{
    type Item = Option<T>;
    type Error = OptionConvertStringError<A::Error, E>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let name = self.name();
        let Self { arg, f } = self;
        match arg.get(matches).map_err(OptionConvertStringError::Arg)? {
            None => Ok(None),
            Some(arg_string) => f(arg_string.as_str()).map(Some).map_err(|error| {
                OptionConvertStringError::FailedToConvert {
                    name,
                    arg_string,
                    error,
                }
            }),
        }
    }
}

pub struct VecConvertString<A, F>
where
    A: Arg,
{
    arg: A,
    f: F,
}

#[derive(Debug)]
pub enum VecConvertStringError<A, E> {
    Arg(A),
    FailedToConvert {
        name: String,
        index: usize,
        arg_string: String,
        error: E,
    },
}

impl<A, E> fmt::Display for VecConvertStringError<A, E>
where
    A: fmt::Display,
    E: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Arg(a) => a.fmt(f),
            Self::FailedToConvert {
                name,
                index,
                arg_string,
                error,
            } => write!(
                f,
                "failed to convert argument \"{}\" in position ({}). \"{}\" could not be parsed (error: {})",
                name, index, arg_string, error
            ),
        }
    }
}

impl<A, F, T, E> Arg for VecConvertString<A, F>
where
    A: Arg<Item = Vec<String>>,
    F: FnMut(&str) -> Result<T, E>,
    E: fmt::Display + fmt::Debug,
{
    type Item = Vec<T>;
    type Error = VecConvertStringError<A::Error, E>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let name = self.name();
        let Self { arg, mut f } = self;
        let mut vec_string = arg.get(matches).map_err(VecConvertStringError::Arg)?;
        let mut vec_t = Vec::with_capacity(vec_string.len());
        for (index, arg_string) in vec_string.drain(..).enumerate() {
            let t = f(arg_string.as_str()).map_err(|error| {
                VecConvertStringError::FailedToConvert {
                    name: name.clone(),
                    index,
                    error,
                    arg_string,
                }
            })?;
            vec_t.push(t);
        }
        Ok(vec_t)
    }
}

pub struct Depend<A, B>
where
    A: Arg,
    B: Arg,
{
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum DependError<A, B> {
    A(A),
    B(B),
    MissingDependency { a: String, b: String },
}

impl<A, B> fmt::Display for DependError<A, B>
where
    A: fmt::Display,
    B: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::A(a) => a.fmt(f),
            Self::B(b) => b.fmt(f),
            Self::MissingDependency { a, b } => {
                write!(f, "({}) and ({}) must be specified together", a, b)
            }
        }
    }
}

impl<T, U, A, B> Arg for Depend<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<U>>,
{
    type Item = Option<(T, U)>;
    type Error = DependError<A::Error, B::Error>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
        self.b.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let missing_dependency = DependError::MissingDependency {
            a: self.a.name(),
            b: self.b.name(),
        };
        let Self { a, b } = self;
        if let Some(a) = a.get(matches).map_err(DependError::A)? {
            if let Some(b) = b.get(matches).map_err(DependError::B)? {
                Ok(Some((a, b)))
            } else {
                Err(missing_dependency)
            }
        } else if b.get(matches).map_err(DependError::B)?.is_some() {
            Err(missing_dependency)
        } else {
            Ok(None)
        }
    }
}

pub struct SomeIf<A, T>
where
    A: Arg,
{
    arg: A,
    t: T,
}

impl<A, T> Arg for SomeIf<A, T>
where
    A: Arg<Item = bool>,
{
    type Item = Option<T>;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        if self.arg.get(matches)? {
            Ok(Some(self.t))
        } else {
            Ok(None)
        }
    }
}

pub fn flag(short: &str, long: &str, doc: &str) -> impl Arg<Item = bool> {
    Flag::new(short, long, doc)
}

pub fn opt<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> impl Arg<Item = Option<T>>
where
    T: FromStr,
    <T as FromStr>::Err: fmt::Debug + fmt::Display,
{
    Opt::new(short, long, doc, hint).option_convert_string(|s| s.parse())
}

pub fn free<T>() -> impl Arg<Item = Vec<T>>
where
    T: FromStr,
    <T as FromStr>::Err: fmt::Debug + fmt::Display,
{
    Free.vec_convert_string(|s| s.parse())
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
macro_rules! args_choice {
    ( $only:expr ) => {
        $only
    };
    ( $head:expr, $($tail:expr),* $(,)* ) => {
        $head $( .choice($tail) )*
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
macro_rules! args_depend {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        assert_eq!(
            opt::<u32>("f", "foo", "", "")
                .required()
                .parse_specified("".to_string(), &["--foo", "42"])
                .result
                .unwrap(),
            42
        );
    }

    #[test]
    fn basic_macros() {
        assert_eq!(
            args_map! {
                let {
                    a = opt::<u32>("f", "foo", "", "").required();
                    b = opt::<u32>("b", "bar", "", "").required();
                } in {
                    a + b
                }
            }
            .parse_specified("".to_string(), &["--foo", "7", "--bar", "9"])
            .result
            .unwrap(),
            16
        );
    }

    #[test]
    fn depend() {
        assert_eq!(
            args_depend! {
                opt::<u32>("f", "foo", "", ""),
                opt::<u32>("b", "bar", "", ""),
            }
            .required()
            .map(|(a, b)| a + b)
            .parse_specified("".to_string(), &["--foo", "7", "--bar", "9"])
            .result
            .unwrap(),
            16
        );
    }

    #[test]
    fn choice() {
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum E {
            A,
            B,
            C(String),
        }
        let choice = args_choice! {
            flag("a", "", "").some_if(E::A),
            flag("b", "", "").some_if(E::B),
            opt("c", "", "", "").option_map(|s| E::C(s)),
        }
        .required()
        .parse_specified("".to_string(), &["-c", "foo"])
        .result
        .unwrap();
        assert_eq!(choice, E::C("foo".to_string()));
    }

    #[test]
    fn validate() {
        let has_empty_switch = args_all! {
            opt::<String>("", "", "doc", "hint"),
            opt::<String>("c", "control", "", ""),
        };
        assert_eq!(
            has_empty_switch.validate().unwrap_err(),
            Invalid {
                has_empty_switch: true,
                ..Default::default()
            }
        );
        let duplicate_switches = args_all! {
            opt::<String>("a", "aa", "", ""),
            opt::<String>("b", "aa", "", ""),
            opt::<String>("a", "bb", "", ""),
            opt::<String>("c", "control", "", ""),
        };
        assert_eq!(
            duplicate_switches.validate().unwrap_err(),
            Invalid {
                duplicate_shorts: vec!["a".to_string()],
                duplicate_longs: vec!["aa".to_string()],
                ..Default::default()
            }
        );
        let invalid_switches = args_all! {
            opt::<String>("aa", "", "", ""),
            opt::<String>("", "a", "", ""),
            opt::<String>("a", "b", "", ""),
            opt::<String>("bb", "aa", "", ""),
            opt::<String>("c", "control", "", ""),
        };
        assert_eq!(
            invalid_switches.validate().unwrap_err(),
            Invalid {
                one_char_longs: vec!["a".to_string(), "b".to_string()],
                multi_char_shorts: vec!["aa".to_string(), "bb".to_string()],
                ..Default::default()
            }
        );
    }
}
