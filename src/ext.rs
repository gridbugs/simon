use arg::*;
use std::env;
use std::ffi::OsStr;
use std::fmt::{self, Debug, Display};
use std::iter::FromIterator;
use util::*;
use validation::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TryMapError<A, M> {
    Arg(A),
    Map(M),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingCodependantArg {
    pub supplied: String,
    pub missing: String,
}

pub type DependError<A, B> = TryMapError<BothError<A, B>, MissingCodependantArg>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultipleMutuallyExclusiveArgs(String, String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingRequiredArg(String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConvertFailed<V, E> {
    name: String,
    error: E,
    value: V,
}

#[derive(Debug)]
pub enum HelpOr<T> {
    Help,
    Value(T),
}

impl<A, M> Display for TryMapError<A, M>
where
    A: Display,
    M: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            TryMapError::Arg(a) => a.fmt(f),
            TryMapError::Map(m) => m.fmt(f),
        }
    }
}

impl Display for MissingCodependantArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} and {} must be supplied together or not at all ({} is supplied, {} is \
             missing)",
            self.supplied, self.missing, self.supplied, self.missing
        )
    }
}

impl Display for MultipleMutuallyExclusiveArgs {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} and {} are mutually exclusive but both were supplied",
            self.0, self.1
        )
    }
}

impl Display for MissingRequiredArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{} is required but not supplied", self.0)
    }
}

impl<V, E> Display for ConvertFailed<V, E>
where
    V: Display,
    E: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "invalid value \"{}\" supplied for \"{}\" ({})",
            self.value, self.name, self.error
        )
    }
}

pub struct ArgExt<A> {
    arg: A,
}

pub fn ext<A: Arg>(arg: A) -> ArgExt<A> {
    ArgExt { arg }
}

impl<A> Arg for ArgExt<A>
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
    fn parse<I>(&self, args: I) -> (Result<Self::Item, TopLevelError<Self::Error>>, Usage)
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        self.arg.parse(args)
    }
}

struct ResultMap<A, F> {
    a: A,
    f: F,
}

impl<A, F, U, E> Arg for ResultMap<A, F>
where
    A: Arg,
    F: Fn(Result<A::Item, A::Error>) -> Result<U, E>,
    E: Debug + Display,
{
    type Item = U;
    type Error = E;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
    }
    fn name(&self) -> String {
        self.a.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        (self.f)(self.a.get(matches))
    }
}

struct ResultBoth<A, B> {
    a: A,
    b: B,
}

#[derive(Debug, PartialEq, Eq)]
pub enum BothError<A, B> {
    A(A),
    B(B),
}

impl<A, B> Display for BothError<A, B>
where
    A: Display,
    B: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            BothError::A(a) => a.fmt(f),
            BothError::B(b) => b.fmt(f),
        }
    }
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

struct TryMap<A, F> {
    a: A,
    f: F,
}
impl<A, U, E, F> Arg for TryMap<A, F>
where
    A: Arg,
    E: Debug + Display,
    F: Fn(A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = TryMapError<A::Error, E>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
    }
    fn name(&self) -> String {
        self.a.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        self.a
            .get(matches)
            .map_err(TryMapError::Arg)
            .and_then(|o| (self.f)(o).map_err(TryMapError::Map))
    }
}

struct Map<A, F> {
    a: A,
    f: F,
}
impl<A, U, F> Arg for Map<A, F>
where
    A: Arg,
    F: Fn(A::Item) -> U,
{
    type Item = U;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
    }
    fn name(&self) -> String {
        self.a.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        self.a.get(matches).map(&self.f)
    }
}

struct OptionMap<A, F> {
    a: A,
    f: F,
}
impl<A, T, U, F> Arg for OptionMap<A, F>
where
    A: Arg<Item = Option<T>>,
    F: Fn(T) -> U,
{
    type Item = Option<U>;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
    }
    fn name(&self) -> String {
        self.a.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        self.a.get(matches).map(|v| v.map(&self.f))
    }
}

struct OptionTryMap<A, F> {
    a: A,
    f: F,
}
impl<A, T, U, E, F> Arg for OptionTryMap<A, F>
where
    A: Arg<Item = Option<T>>,
    F: Fn(T) -> Result<U, E>,
    E: Debug + Display,
{
    type Item = Option<U>;
    type Error = TryMapError<A::Error, E>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
    }
    fn name(&self) -> String {
        self.a.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        match self.a.get(matches).map_err(TryMapError::Arg)? {
            None => Ok(None),
            Some(x) => (self.f)(x).map_err(TryMapError::Map).map(Some),
        }
    }
}

struct EitherOrBothAny<A, B> {
    a: A,
    b: B,
}
impl<A, B, T, U> Arg for EitherOrBothAny<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<U>>,
{
    type Item = Option<EitherOrBoth<T, U>>;
    type Error = BothError<A::Error, B::Error>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
        self.b.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let a = self.a.get(matches).map_err(BothError::A)?;
        let b = self.b.get(matches).map_err(BothError::B)?;
        Ok(match (a, b) {
            (None, None) => None,
            (Some(l), None) => Some(EitherOrBoth::Either(Either::Left(l))),
            (None, Some(r)) => Some(EitherOrBoth::Either(Either::Right(r))),
            (Some(l), Some(r)) => Some(EitherOrBoth::Both(l, r)),
        })
    }
}

struct EitherAny<A, B> {
    a: A,
    b: B,
}
impl<A, B, T, U> Arg for EitherAny<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<U>>,
{
    type Item = Option<Either<T, U>>;
    type Error =
        TryMapError<BothError<A::Error, B::Error>, MultipleMutuallyExclusiveArgs>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
        self.b.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let a = self.a
            .get(matches)
            .map_err(|e| TryMapError::Arg(BothError::A(e)))?;
        let b = self.b
            .get(matches)
            .map_err(|e| TryMapError::Arg(BothError::B(e)))?;
        match (a, b) {
            (None, None) => Ok(None),
            (Some(l), None) => Ok(Some(Either::Left(l))),
            (None, Some(r)) => Ok(Some(Either::Right(r))),
            (Some(_), Some(_)) => Err(TryMapError::Map(MultipleMutuallyExclusiveArgs(
                self.a.name(),
                self.b.name(),
            ))),
        }
    }
}

struct EitherC<A, B> {
    a: A,
    b: B,
}
impl<A, B, T> Arg for EitherC<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<T>>,
{
    type Item = Option<T>;
    type Error =
        TryMapError<BothError<A::Error, B::Error>, MultipleMutuallyExclusiveArgs>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
        self.b.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let a = self.a
            .get(matches)
            .map_err(|e| TryMapError::Arg(BothError::A(e)))?;
        let b = self.b
            .get(matches)
            .map_err(|e| TryMapError::Arg(BothError::B(e)))?;
        match (a, b) {
            (None, None) => Ok(None),
            (Some(l), None) => Ok(Some(l)),
            (None, Some(r)) => Ok(Some(r)),
            (Some(_), Some(_)) => Err(TryMapError::Map(MultipleMutuallyExclusiveArgs(
                self.a.name(),
                self.b.name(),
            ))),
        }
    }
}

struct VecTryMap<A, F> {
    a: A,
    f: F,
}
impl<A, I, U, E, F> Arg for VecTryMap<A, F>
where
    I: IntoIterator,
    A: Arg<Item = I>,
    E: Debug + Display,
    F: Fn(I::Item) -> Result<U, E>,
{
    type Item = Vec<U>;
    type Error = TryMapError<A::Error, E>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
    }
    fn name(&self) -> String {
        self.a.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let mut vec = Vec::new();
        for x in self.a.get(matches).map_err(TryMapError::Arg)? {
            vec.push((self.f)(x).map_err(TryMapError::Map)?);
        }
        Ok(vec)
    }
}

struct VecMap<A, F> {
    a: A,
    f: F,
}
impl<A, I, U, F> Arg for VecMap<A, F>
where
    I: IntoIterator,
    A: Arg<Item = I>,
    F: Fn(I::Item) -> U,
{
    type Item = Vec<U>;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
    }
    fn name(&self) -> String {
        self.a.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.a.get(matches)?.into_iter().map(&self.f).collect())
    }
}

struct Both<A, B> {
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
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok((
            self.a.get(matches).map_err(BothError::A)?,
            self.b.get(matches).map_err(BothError::B)?,
        ))
    }
}

struct Depend<A, B> {
    a: A,
    b: B,
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
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a
            .get(matches)
            .map_err(|e| TryMapError::Arg(BothError::A(e)))?;
        let maybe_b = self.b
            .get(matches)
            .map_err(|e| TryMapError::Arg(BothError::B(e)))?;
        match (maybe_a, maybe_b) {
            (Some(a), Some(b)) => Ok(Some((a, b))),
            (None, None) => Ok(None),
            (Some(_), None) => Err(TryMapError::Map(MissingCodependantArg {
                supplied: self.a.name(),
                missing: self.b.name(),
            })),
            (None, Some(_)) => Err(TryMapError::Map(MissingCodependantArg {
                supplied: self.b.name(),
                missing: self.a.name(),
            })),
        }
    }
}

struct Rename<A> {
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

#[derive(PartialEq, Eq, Debug)]
pub enum ValidError<A> {
    Arg(A),
    Invalid(Invalid),
}

impl<A> Display for ValidError<A>
where
    A: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ValidError::Arg(a) => a.fmt(f),
            ValidError::Invalid(i) => fmt::Display::fmt(i, f),
        }
    }
}

impl<A> Arg for Valid<A>
where
    A: Arg,
{
    type Item = A::Item;
    type Error = ValidError<A::Error>;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches).map_err(ValidError::Arg)
    }
    fn parse<I>(&self, args: I) -> (Result<Self::Item, TopLevelError<Self::Error>>, Usage)
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        if let Some(invalid) = self.validate() {
            (
                Err(TopLevelError::Other(ValidError::Invalid(invalid))),
                Usage::empty(),
            )
        } else {
            parse_ignore_validation(self, args)
        }
    }
}

impl<A> ArgExt<A>
where
    A: Arg,
{
    pub fn parse<I>(&self, args: I) -> (Result<A::Item, TopLevelError<A::Error>>, Usage)
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        self.arg.parse(args)
    }
    pub fn parse_env(
        &self,
        program_name: ProgramName,
    ) -> (
        Result<A::Item, TopLevelError<A::Error>>,
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
    pub fn parse_env_default(
        &self,
    ) -> (
        Result<A::Item, TopLevelError<A::Error>>,
        UsageWithProgramName,
    ) {
        self.parse_env(Default::default())
    }

    pub fn just_parse<I>(&self, args: I) -> Result<A::Item, TopLevelError<A::Error>>
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        self.parse(args).0
    }

    pub fn just_parse_env(
        &self,
        program_name: ProgramName,
    ) -> Result<A::Item, TopLevelError<A::Error>> {
        self.parse_env(program_name).0
    }

    pub fn just_parse_env_default(&self) -> Result<A::Item, TopLevelError<A::Error>> {
        self.parse_env_default().0
    }

    pub fn result_map<F, U, E>(self, f: F) -> ArgExt<impl Arg<Item = U, Error = E>>
    where
        E: Debug + Display,
        F: Fn(Result<A::Item, A::Error>) -> Result<U, E>,
    {
        ext(ResultMap { a: self.arg, f })
    }
    pub fn result_both<B>(
        self,
        b: B,
    ) -> ArgExt<
        impl Arg<Item = (Result<A::Item, A::Error>, Result<B::Item, B::Error>), Error = Never>,
    >
    where
        B: Arg,
        Self: Sized,
    {
        ext(ResultBoth { a: self.arg, b })
    }

    pub fn both<B>(
        self,
        b: B,
    ) -> ArgExt<impl Arg<Item = (A::Item, B::Item), Error = BothError<A::Error, B::Error>>>
    where
        B: Arg,
    {
        ext(Both { a: self.arg, b })
    }
    pub fn try_map<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = U, Error = TryMapError<A::Error, E>>>
    where
        E: Debug + Display,
        F: Fn(A::Item) -> Result<U, E>,
    {
        ext(TryMap { a: self.arg, f })
    }
    pub fn map<F, U>(self, f: F) -> ArgExt<impl Arg<Item = U, Error = A::Error>>
    where
        F: Fn(A::Item) -> U,
    {
        ext(Map { a: self.arg, f })
    }
    pub fn convert<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<
        impl Arg<Item = U, Error = TryMapError<A::Error, ConvertFailed<A::Item, E>>>,
    >
    where
        A::Item: Clone + Debug + Display,
        E: Clone + Debug + Display,
        F: Fn(A::Item) -> Result<U, E>,
    {
        let name = self.name();
        self.try_map(move |value| {
            let name = name.clone();
            f(value.clone()).map_err(move |error| ConvertFailed { error, name, value })
        })
    }
    pub fn with_help(self, flag: Flag) -> ArgExt<impl Arg<Item = HelpOr<A::Item>>> {
        ext(flag).unless(self.arg).map(|x| match x {
            None => HelpOr::Help,
            Some(x) => HelpOr::Value(x),
        })
    }
    pub fn with_help_default(self) -> ArgExt<impl Arg<Item = HelpOr<A::Item>>> {
        self.with_help(Flag::new("h", "help", "print this help menu"))
    }
    pub fn rename(
        self,
        name: &str,
    ) -> ArgExt<impl Arg<Item = A::Item, Error = A::Error>> {
        ext(Rename {
            arg: self.arg,
            name: name.to_string(),
        })
    }
    pub fn valid(self) -> ArgExt<Valid<A>> {
        ext(Valid { arg: self.arg })
    }
}

impl<A, B> ArgExt<A>
where
    A: Arg<Item = HelpOr<B>>,
{
    pub fn parse_env_or_exit(&self, program_name: ProgramName) -> B {
        match self.parse_env(program_name) {
            (Ok(HelpOr::Value(args)), _usage) => args,
            (Ok(HelpOr::Help), usage) => {
                print!("{}", usage.render());
                ::std::process::exit(0);
            }
            (Err(error), usage) => {
                print!("{}\n\n", error);
                print!("{}", usage.render());
                ::std::process::exit(1);
            }
        }
    }
    pub fn parse_env_default_or_exit(&self) -> B {
        self.parse_env_or_exit(Default::default())
    }
}

impl<A, T> ArgExt<A>
where
    A: Arg<Item = Option<T>>,
{
    pub fn depend<B, U>(
        self,
        b: B,
    ) -> ArgExt<impl Arg<Item = Option<(T, U)>, Error = DependError<A::Error, B::Error>>>
    where
        B: Arg<Item = Option<U>>,
    {
        ext(Depend { a: self.arg, b })
    }
    pub fn otherwise<U>(self, b: U) -> ArgExt<impl Arg<Item = Either<T, U::Item>>>
    where
        U: Arg,
    {
        self.result_both(b).result_map(|r| {
            let (a, b) = Never::result_ok(r);
            match a.map_err(Either::Left)? {
                Some(a) => Ok(Either::Left(a)),
                None => b.map(Either::Right).map_err(Either::Right),
            }
        })
    }
    pub fn option_try_map<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = Option<U>, Error = TryMapError<A::Error, E>>>
    where
        E: Debug + Display,
        F: Fn(T) -> Result<U, E>,
    {
        ext(OptionTryMap { a: self.arg, f })
    }
    pub fn option_map<F, U>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = Option<U>, Error = A::Error>>
    where
        F: Fn(T) -> U,
    {
        ext(OptionMap { a: self.arg, f })
    }
    pub fn either_or_both_any<B, U>(
        self,
        b: B,
    ) -> ArgExt<impl Arg<Item = Option<EitherOrBoth<T, U>>>>
    where
        B: Arg<Item = Option<U>>,
    {
        ext(EitherOrBothAny { a: self.arg, b })
    }
    pub fn either_any<B, U>(self, b: B) -> ArgExt<impl Arg<Item = Option<Either<T, U>>>>
    where
        B: Arg<Item = Option<U>>,
    {
        ext(EitherAny { a: self.arg, b })
    }
    pub fn either<B>(self, b: B) -> ArgExt<impl Arg<Item = Option<T>>>
    where
        B: Arg<Item = Option<T>>,
    {
        ext(EitherC { a: self.arg, b })
    }
    pub fn with_default_lazy<F: Fn() -> T>(self, f: F) -> ArgExt<impl Arg<Item = T>> {
        self.map(move |x| x.unwrap_or_else(&f))
    }
    pub fn with_default(self, t: T) -> ArgExt<impl Arg<Item = T>>
    where
        T: Clone,
    {
        self.with_default_lazy(move || t.clone())
    }
    pub fn required(
        self,
    ) -> ArgExt<impl Arg<Item = T, Error = TryMapError<A::Error, MissingRequiredArg>>>
    {
        let name = self.name();
        self.try_map(move |x| match x {
            Some(x) => Ok(x),
            None => Err(MissingRequiredArg(name.clone())),
        })
    }
    pub fn option_convert<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<
        impl Arg<Item = Option<U>, Error = TryMapError<A::Error, ConvertFailed<T, E>>>,
    >
    where
        T: Clone + Debug + Display,
        E: Clone + Debug + Display,
        F: Fn(T) -> Result<U, E>,
    {
        let name = self.name();
        self.option_try_map(move |value| {
            let name = name.clone();
            f(value.clone()).map_err(move |error| ConvertFailed { error, name, value })
        })
    }
}

impl<A> ArgExt<A>
where
    A: Arg<Item = bool>,
{
    pub fn some_if<T>(self, t: T) -> ArgExt<impl Arg<Item = Option<T>>>
    where
        T: Clone,
    {
        self.map(move |b| if b { Some(t.clone()) } else { None })
    }
    pub fn unit_option(self) -> ArgExt<impl Arg<Item = Option<()>>> {
        self.map(|b| if b { Some(()) } else { None })
    }
    pub fn unless<U>(self, b: U) -> ArgExt<impl Arg<Item = Option<U::Item>>>
    where
        U: Arg,
    {
        self.result_both(b).result_map(|r| {
            let (a, b) = Never::result_ok(r);
            if a.map_err(Either::Left)? {
                Ok(None)
            } else {
                b.map(Some).map_err(Either::Right)
            }
        })
    }
}

impl<A, I> ArgExt<A>
where
    A: Arg<Item = I>,
    I: IntoIterator,
{
    pub fn into_iter(self) -> ArgExt<impl Arg<Item = I::IntoIter>> {
        self.map(|i| i.into_iter())
    }
    pub fn vec_try_map<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = Vec<U>, Error = TryMapError<A::Error, E>>>
    where
        E: Debug + Display,
        F: Fn(I::Item) -> Result<U, E>,
    {
        ext(VecTryMap { a: self.arg, f })
    }
    pub fn vec_map<F, U>(self, f: F) -> ArgExt<impl Arg<Item = Vec<U>, Error = A::Error>>
    where
        F: Fn(I::Item) -> U,
    {
        ext(VecMap { a: self.arg, f })
    }
    pub fn vec_convert<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<
        impl Arg<Item = Vec<U>, Error = TryMapError<A::Error, ConvertFailed<I::Item, E>>>,
    >
    where
        I::Item: Clone + Debug + Display,
        E: Clone + Debug + Display,
        F: Fn(I::Item) -> Result<U, E>,
    {
        let name = self.name();
        self.vec_try_map(move |value| {
            let name = name.clone();
            f(value.clone()).map_err(move |error| ConvertFailed { error, name, value })
        })
    }
}

impl<A, I, T, E> ArgExt<A>
where
    E: Debug + Display,
    A: Arg<Item = I>,
    I: IntoIterator<Item = Result<T, E>>,
{
    pub fn vec_ok_or_first_err(
        self,
    ) -> ArgExt<impl Arg<Item = Vec<T>, Error = TryMapError<A::Error, E>>> {
        self.try_map(|i| {
            let mut vec = Vec::new();
            for x in i {
                vec.push(x?);
            }
            Ok(vec)
        })
    }
}

impl<A, I> ArgExt<A>
where
    A: Arg<Item = I>,
    I: Iterator,
{
    pub fn collect<C>(self) -> ArgExt<impl Arg<Item = C>>
    where
        C: FromIterator<I::Item>,
    {
        self.map(|i| i.collect())
    }
}
