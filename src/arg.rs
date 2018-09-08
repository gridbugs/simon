use std::ops::Deref;
use getopts;
use util::*;

pub enum SwitchArity {
    Flag,
    MultiFlag,
    Opt { hint: String },
    MultiOpt,
}

#[derive(Clone)]
pub struct SwitchCommon {
    pub short: String,
    pub long: String,
    pub doc: String,
}

pub trait Switches {
    fn add(&mut self, common: SwitchCommon, arity: SwitchArity);
}

pub type Matches = getopts::Matches;

pub trait Arg {
    type Item;
    type Error;
    fn update_switches<S: Switches>(&self, switches: &mut S);
    fn name(&self) -> String;
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error>;
    fn result_map<F, U, E>(self, f: F) -> ResultMap<Self, F>
    where
        F: Fn(Result<Self::Item, Self::Error>) -> Result<U, E>,
        Self: Sized,
    {
        ResultMap { arg: self, f }
    }
    fn result_both<B>(self, b: B) -> ResultBoth<Self, B>
    where
        B: Arg,
        Self: Sized,
    {
        ResultBoth { a: self, b }
    }
}

pub struct ResultMap<A, F> {
    arg: A,
    f: F,
}

impl<A, F, U, E> Arg for ResultMap<A, F>
where
    A: Arg,
    F: Fn(Result<A::Item, A::Error>) -> Result<U, E>,
{
    type Item = U;
    type Error = E;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        (self.f)(self.arg.get(matches))
    }
}

pub struct ResultBoth<A, B> {
    a: A,
    b: B,
}

pub enum BothError<A, B> {
    A(A),
    B(B),
}

impl<A, B> Arg for ResultBoth<A, B>
where
    A: Arg,
    B: Arg,
{
    type Item = (Result<A::Item, A::Error>, Result<B::Item, B::Error>);
    type Error = Never;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
        self.b.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok((self.a.get(matches), self.b.get(matches)))
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

impl Arg for MultiOpt {
    type Item = Vec<String>;
    type Error = Never;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        switches.add(self.opt.common.clone(), SwitchArity::MultiOpt);
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

pub struct Rename<A> {
    arg: A,
    name: String,
}

impl<A> Arg for Rename<A>
where
    A: Arg,
{
    type Item = A::Item;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.name.clone()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches)
    }
}

pub struct Valid<A> {
    arg: A,
}

impl<A> Arg for Valid<A>
where
    A: Arg,
{
    type Item = A::Item;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches)
    }
}
