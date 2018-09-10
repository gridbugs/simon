use getopts;
use std::env;
use std::ffi::OsStr;
use std::fmt::{self, Debug, Display};
use std::ops::Deref;
use util::*;
use validation::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SwitchArity {
    Flag,
    MultiFlag,
    Opt { hint: String },
    MultiOpt { hint: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
}

pub trait Switches {
    fn add(&mut self, common: SwitchCommon, arity: SwitchArity);
}

impl Switches for getopts::Options {
    fn add(&mut self, common: SwitchCommon, arity: SwitchArity) {
        match arity {
            SwitchArity::Flag => {
                self.optflag(
                    common.short.as_str(),
                    common.long.as_str(),
                    common.doc.as_str(),
                );
            }
            SwitchArity::MultiFlag => {
                self.optflagmulti(
                    common.short.as_str(),
                    common.long.as_str(),
                    common.doc.as_str(),
                );
            }
            SwitchArity::Opt { hint } => {
                self.optopt(
                    common.short.as_str(),
                    common.long.as_str(),
                    common.doc.as_str(),
                    hint.as_str(),
                );
            }
            SwitchArity::MultiOpt { hint } => {
                self.optmulti(
                    common.short.as_str(),
                    common.long.as_str(),
                    common.doc.as_str(),
                    hint.as_str(),
                );
            }
        }
    }
}

pub type Matches = getopts::Matches;

#[derive(Debug, PartialEq, Eq)]
pub enum TopLevelError<E> {
    Getopts(getopts::Fail),
    Other(E),
}

impl<E: Display> Display for TopLevelError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            TopLevelError::Getopts(fail) => fmt::Display::fmt(&fail, f),
            TopLevelError::Other(other) => fmt::Display::fmt(&other, f),
        }
    }
}

pub enum ProgramName {
    Literal(String),
    ReadArg0,
}

impl Default for ProgramName {
    fn default() -> Self {
        ProgramName::ReadArg0
    }
}

pub struct Usage {
    opts: getopts::Options,
}

impl Usage {
    pub fn empty() -> Self {
        Self {
            opts: getopts::Options::new(),
        }
    }
    pub fn render(&self, brief: &str) -> String {
        self.opts.usage(brief)
    }
}

pub struct UsageWithProgramName {
    pub usage: Usage,
    pub program_name: String,
}

impl UsageWithProgramName {
    pub fn render(&self) -> String {
        let brief = format!("Usage: {} [options]", &self.program_name);
        self.usage.render(&brief)
    }
    pub fn render_with_brief<F: Fn(&str) -> String>(
        &self,
        brief_given_program_name: F,
    ) -> String {
        self.usage
            .render(brief_given_program_name(self.program_name.as_str()).as_str())
    }
}

pub fn parse_ignore_validation<A, I>(
    arg: &A,
    args: I,
) -> (Result<A::Item, TopLevelError<A::Error>>, Usage)
where
    A: Arg + ?Sized,
    I: IntoIterator,
    I::Item: AsRef<OsStr>,
{
    let mut opts = getopts::Options::new();
    arg.update_switches(&mut opts);
    (
        opts.parse(args)
            .map_err(TopLevelError::Getopts)
            .and_then(|matches| arg.get(&matches).map_err(TopLevelError::Other)),
        Usage { opts },
    )
}

pub trait Arg {
    type Item;
    type Error: Debug + Display;
    fn update_switches<S: Switches>(&self, switches: &mut S);
    fn name(&self) -> String;
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error>;
    fn validate(&self) -> Option<Invalid> {
        let mut checker = Checker::default();
        self.update_switches(&mut checker);
        checker.invalid()
    }
    fn parse<I>(&self, args: I) -> (Result<Self::Item, TopLevelError<Self::Error>>, Usage)
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        if let Some(invalid) = self.validate() {
            panic!("Invalid command spec:\n{}", invalid);
        }
        parse_ignore_validation(self, args)
    }

    fn parse_env(
        &self,
        program_name: ProgramName,
    ) -> (
        Result<Self::Item, TopLevelError<Self::Error>>,
        UsageWithProgramName,
    ) {
        let args: Vec<String> = env::args().collect();
        let program_name = match program_name {
            ProgramName::Literal(program_name) => program_name.clone(),
            ProgramName::ReadArg0 => args[0].clone(),
        };

        let (result, usage) = self.parse(&args[1..]);

        let usage_with_program_name = UsageWithProgramName {
            usage,
            program_name,
        };

        (result, usage_with_program_name)
    }
    fn parse_env_default(
        &self,
    ) -> (
        Result<Self::Item, TopLevelError<Self::Error>>,
        UsageWithProgramName,
    ) {
        self.parse_env(Default::default())
    }

    fn just_parse<I>(&self, args: I) -> Result<Self::Item, TopLevelError<Self::Error>>
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        self.parse(args).0
    }

    fn just_parse_env(
        &self,
        program_name: ProgramName,
    ) -> Result<Self::Item, TopLevelError<Self::Error>> {
        self.parse_env(program_name).0
    }

    fn just_parse_env_default(&self) -> Result<Self::Item, TopLevelError<Self::Error>> {
        self.parse_env_default().0
    }
}

impl<A, D> Arg for D
where
    A: Arg,
    D: Deref<Target = A>,
{
    type Item = A::Item;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.deref().update_switches(switches);
    }
    fn name(&self) -> String {
        self.deref().name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        self.deref().get(matches)
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

impl<T> Arg for Value<T>
where
    T: Clone,
{
    type Item = T;
    type Error = Never;
    fn update_switches<S: Switches>(&self, _switches: &mut S) {}
    fn name(&self) -> String {
        self.name.clone()
    }
    fn get(&self, _matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.value.clone())
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
        switches.add(self.common.clone(), SwitchArity::Flag);
    }
    fn name(&self) -> String {
        self.common.long.clone()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_present(self.common.long.as_str()))
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
            SwitchArity::Opt {
                hint: self.hint.clone(),
            },
        );
    }
    fn name(&self) -> String {
        self.common.long.clone()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_str(self.common.long.as_str()))
    }
}

pub struct MultiFlag {
    flag: Flag,
}

impl MultiFlag {
    pub fn new(short: &str, long: &str, doc: &str) -> Self {
        Self {
            flag: Flag::new(short, long, doc),
        }
    }
}

impl Arg for MultiFlag {
    type Item = usize;
    type Error = Never;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        switches.add(self.flag.common.clone(), SwitchArity::MultiFlag);
    }
    fn name(&self) -> String {
        self.flag.common.long.clone()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_count(self.flag.common.long.as_str()))
    }
}

pub struct MultiOpt {
    opt: Opt,
}

impl MultiOpt {
    pub fn new(short: &str, long: &str, doc: &str, hint: &str) -> Self {
        Self {
            opt: Opt::new(short, long, doc, hint),
        }
    }
}

impl Arg for MultiOpt {
    type Item = Vec<String>;
    type Error = Never;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        switches.add(
            self.opt.common.clone(),
            SwitchArity::MultiOpt {
                hint: self.opt.hint.clone(),
            },
        );
    }
    fn name(&self) -> String {
        self.opt.common.long.clone()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_strs(self.opt.common.long.as_str()))
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
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.free.clone())
    }
}
