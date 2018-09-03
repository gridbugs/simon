extern crate getopts;

use std::env;
use std::ffi::OsStr;
use std::fmt::{self, Debug, Display, Write};
use std::rc::Rc;
use std::str::FromStr;

#[derive(Debug)]
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

impl<T> From<getopts::Fail> for TopLevelError<T> {
    fn from(f: getopts::Fail) -> Self {
        TopLevelError::Getopts(f)
    }
}

#[derive(Clone)]
pub enum Note {
    DefaultValue(String),
    Dependency(String),
    Required,
}

#[must_use]
#[derive(Clone)]
enum NoteList {
    Empty,
    Cons(Rc<(Note, NoteList)>),
}

#[derive(Clone, Copy)]
pub struct WhichNotes {
    pub default_value: bool,
    pub dependency: bool,
    pub required: bool,
}

impl WhichNotes {
    pub fn all() -> Self {
        Self {
            default_value: true,
            dependency: true,
            required: true,
        }
    }
    pub fn none() -> Self {
        Self {
            default_value: false,
            dependency: false,
            required: false,
        }
    }
}
impl Default for WhichNotes {
    fn default() -> Self {
        Self::all()
    }
}

#[derive(Clone)]
pub struct Notes {
    list: NoteList,
    pub which_notes_to_document: WhichNotes,
}

impl Note {
    fn append(&self, which_notes: WhichNotes, buf: &mut String) {
        match self {
            Note::DefaultValue(d) => if which_notes.default_value {
                write!(buf, "Default: {}", d).unwrap();
            },
            Note::Dependency(c) => if which_notes.dependency {
                write!(buf, "Dependency: {}", c).unwrap();
            },
            Note::Required => if which_notes.required {
                write!(buf, "Required").unwrap();
            },
        }
    }
}

impl NoteList {
    fn new() -> Self {
        NoteList::Empty
    }
    fn push(self, note: Note) -> Self {
        NoteList::Cons(Rc::new((note, self)))
    }
    fn append_rec(&self, sep: &str, which_notes: WhichNotes, buf: &mut String) {
        match self {
            NoteList::Empty => (),
            NoteList::Cons(node) => {
                write!(buf, "{}", sep).unwrap();
                node.0.append(which_notes, buf);
                node.1.append_rec(sep, which_notes, buf);
            }
        }
    }
}

impl Notes {
    pub fn new(which_notes_to_document: WhichNotes) -> Self {
        Self {
            list: NoteList::new(),
            which_notes_to_document,
        }
    }
    pub fn push(self, note: Note) -> Self {
        Self {
            list: self.list.push(note),
            ..self
        }
    }
    fn append(&self, buf: &mut String) {
        match &self.list {
            NoteList::Empty => (),
            NoteList::Cons(node) => {
                write!(buf, " (").unwrap();
                node.0.append(self.which_notes_to_document, buf);
                node.1
                    .append_rec(", ", self.which_notes_to_document, buf);
                write!(buf, ")").unwrap();
            }
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

pub trait Arg {
    type Item;
    type Error: Debug + Display;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes);
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error>;
    fn name(&self) -> String;
    fn parse<C: IntoIterator>(
        &self,
        args: C,
        which_notes_to_document: WhichNotes,
    ) -> (Result<Self::Item, TopLevelError<Self::Error>>, Usage)
    where
        C::Item: AsRef<OsStr>,
    {
        let mut opts = getopts::Options::new();
        self.update_options(&mut opts, Notes::new(which_notes_to_document));
        (
            opts.parse(args)
                .map_err(TopLevelError::Getopts)
                .and_then(|matches| self.get(&matches).map_err(TopLevelError::Other)),
            Usage { opts },
        )
    }
    fn parse_env(
        &self,
        which_notes_to_document: WhichNotes,
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

        let (result, usage) = self.parse(&args[1..], which_notes_to_document);

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
        self.parse_env(Default::default(), Default::default())
    }
}

#[derive(Default)]
pub struct Opt {
    pub short: String,
    pub long: String,
    pub hint: String,
    pub doc: String,
}

#[derive(Default)]
pub struct Flag {
    pub short: String,
    pub long: String,
    pub doc: String,
}

impl Flag {
    pub fn default_help() -> Self {
        Self {
            short: "h".to_string(),
            long: "help".to_string(),
            doc: "print this help menu".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Never {}

impl Display for Never {
    fn fmt(&self, _f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            _ => unreachable!(),
        }
    }
}

impl Never {
    fn result_ok<T>(result: Result<T, Never>) -> T {
        match result {
            Err(_) => unreachable!(),
            Ok(t) => t,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A: Display, B: Display> Display for Either<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Either::Left(a) => fmt::Display::fmt(&a, f),
            Either::Right(b) => fmt::Display::fmt(&b, f),
        }
    }
}

impl Arg for Opt {
    type Item = Option<String>;
    type Error = Never;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        let mut doc = self.doc.clone();
        notes.append(&mut doc);
        opts.optopt(
            self.short.as_str(),
            self.long.as_str(),
            doc.as_str(),
            self.hint.as_str(),
        );
    }
    fn name(&self) -> String {
        self.long.clone()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_str(self.long.as_str()))
    }
}

impl Arg for Flag {
    type Item = bool;
    type Error = Never;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        let mut doc = self.doc.clone();
        notes.append(&mut doc);
        opts.optflag(self.short.as_str(), self.long.as_str(), doc.as_str());
    }
    fn name(&self) -> String {
        self.long.clone()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_present(self.long.as_str()))
    }
}

pub struct Map<A, F> {
    arg: A,
    f: F,
}

impl<A, U, F> Arg for Map<A, F>
where
    A: Arg,
    F: Fn(A::Item) -> U,
{
    type Item = U;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches).map(&self.f)
    }
}

pub enum HelpOr<T> {
    Help,
    Value(T),
}

pub struct WithHelp<V> {
    cond: Flag,
    value: V,
}

impl<V> Arg for WithHelp<V>
where
    V: Arg,
{
    type Item = HelpOr<V::Item>;
    type Error = V::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.cond.update_options(opts, notes.clone());
        self.value.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.value.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        if Never::result_ok(self.cond.get(matches)) {
            Ok(HelpOr::Help)
        } else {
            Ok(HelpOr::Value(self.value.get(matches)?))
        }
    }
}

pub struct Otherwise<C, V> {
    cond: C,
    value: V,
}

impl<T, C, V> Arg for Otherwise<C, V>
where
    C: Arg<Item = Option<T>>,
    V: Arg,
{
    type Item = Either<T, V::Item>;
    type Error = Either<C::Error, V::Error>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.cond.update_options(opts, notes.clone());
        self.value.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.value.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        match self.cond.get(matches) {
            Err(e) => Err(Either::Left(e)),
            Ok(o) => match o {
                Some(t) => Ok(Either::Left(t)),
                None => match self.value.get(matches) {
                    Err(e) => Err(Either::Right(e)),
                    Ok(o) => Ok(Either::Right(o)),
                },
            },
        }
    }
}

pub struct SomeIf<A, T> {
    arg: A,
    value: T,
}

impl<A, T> Arg for SomeIf<A, T>
where
    T: Clone,
    A: Arg<Item = bool>,
{
    type Item = Option<T>;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(if self.arg.get(matches)? {
            Some(self.value.clone())
        } else {
            None
        })
    }
}

pub struct TryMap<A, F> {
    arg: A,
    f: F,
}

#[derive(Debug)]
pub enum TryMapError<E, F> {
    Other(E),
    MapFailed(F),
}

impl<E: Display, F: Display> Display for TryMapError<E, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            TryMapError::MapFailed(fail) => fmt::Display::fmt(&fail, f),
            TryMapError::Other(other) => fmt::Display::fmt(&other, f),
        }
    }
}

impl<A, U, E, F> Arg for TryMap<A, F>
where
    A: Arg,
    E: Debug + Display,
    F: Fn(A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = TryMapError<A::Error, E>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(TryMapError::Other)
            .and_then(|o| (self.f)(o).map_err(TryMapError::MapFailed))
    }
}

pub struct OptionMap<A, F> {
    arg: A,
    f: F,
}

impl<A, T, U, F> Arg for OptionMap<A, F>
where
    A: Arg<Item = Option<T>>,
    F: Fn(T) -> U,
{
    type Item = Option<U>;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches).map(|v| v.map(&self.f))
    }
}

pub struct OptionTryMap<A, F> {
    arg: A,
    f: F,
}

impl<T, A, U, E, F> Arg for OptionTryMap<A, F>
where
    A: Arg<Item = Option<T>>,
    E: Debug + Display,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = TryMapError<A::Error, E>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(TryMapError::Other)
            .and_then(|o| match o {
                Some(t) => (self.f)(t).map(Some).map_err(TryMapError::MapFailed),
                None => Ok(None),
            })
    }
}

pub struct Join<A, B> {
    a: A,
    b: B,
}

pub type JoinError<A, B> = Either<A, B>;

impl<A, B> Arg for Join<A, B>
where
    A: Arg,
    B: Arg,
{
    type Item = (A::Item, B::Item);
    type Error = JoinError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.a.update_options(opts, notes.clone());
        self.b.update_options(opts, notes);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok((
            self.a.get(matches).map_err(Either::Left)?,
            self.b.get(matches).map_err(Either::Right)?,
        ))
    }
}

pub struct OptionJoin<A, B> {
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum OptionJoinError<A, B> {
    Left(A),
    Right(B),
    MissingOptionJoinantArg {
        supplied_name: String,
        missing_name: String,
    },
}

impl<A: Display, B: Display> Display for OptionJoinError<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            OptionJoinError::Left(a) => fmt::Display::fmt(&a, f),
            OptionJoinError::Right(b) => fmt::Display::fmt(&b, f),
            OptionJoinError::MissingOptionJoinantArg {
                supplied_name,
                missing_name,
            } => write!(
                f,
                "{} and {} must be supplied together or not at all \
                 ({} is supplied, {} is missing)",
                supplied_name, missing_name, supplied_name, missing_name
            ),
        }
    }
}

impl<T, U, A, B> Arg for OptionJoin<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<U>>,
{
    type Item = Option<(T, U)>;
    type Error = OptionJoinError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        let a_note =
            Note::Dependency(format!("must be specified with {}", self.b.name()));
        let b_note =
            Note::Dependency(format!("must be specified with {}", self.a.name()));
        self.a
            .update_options(opts, notes.clone().push(a_note));
        self.b.update_options(opts, notes.push(b_note));
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(OptionJoinError::Left)?;
        let maybe_b = self.b.get(matches).map_err(OptionJoinError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(a), Some(b)) => Ok(Some((a, b))),
            (None, None) => Ok(None),
            (Some(_), None) => Err(OptionJoinError::MissingOptionJoinantArg {
                supplied_name: self.a.name(),
                missing_name: self.b.name(),
            }),
            (None, Some(_)) => Err(OptionJoinError::MissingOptionJoinantArg {
                supplied_name: self.b.name(),
                missing_name: self.a.name(),
            }),
        }
    }
}

pub struct EitherCombinator<A, B> {
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum EitherError<A, B> {
    Left(A),
    Right(B),
    MultipleMutuallyExclusiveArgs {
        left_name: String,
        right_name: String,
    },
}

impl<A: Display, B: Display> Display for EitherError<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            EitherError::Left(a) => fmt::Display::fmt(&a, f),
            EitherError::Right(b) => fmt::Display::fmt(&b, f),
            EitherError::MultipleMutuallyExclusiveArgs {
                left_name,
                right_name,
            } => write!(
                f,
                "{} and {} are mutually exclusive but both were supplied",
                left_name, right_name
            ),
        }
    }
}

fn either_update_options(
    a: &impl Arg,
    b: &impl Arg,
    opts: &mut getopts::Options,
    notes: Notes,
) {
    let a_note = Note::Dependency(format!("mutually exclusive with {}", b.name()));
    let b_note = Note::Dependency(format!("mutually exclusive with {}", a.name()));
    a.update_options(opts, notes.clone().push(a_note));
    b.update_options(opts, notes.push(b_note));
}

impl<T, U, A, B> Arg for EitherCombinator<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<U>>,
{
    type Item = Option<Either<T, U>>;
    type Error = EitherError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        either_update_options(&self.a, &self.b, opts, notes);
    }
    fn name(&self) -> String {
        format!("({} or {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(EitherError::Left)?;
        let maybe_b = self.b.get(matches).map_err(EitherError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveArgs {
                left_name: self.a.name(),
                right_name: self.b.name(),
            }),
            (Some(a), None) => Ok(Some(Either::Left(a))),
            (None, Some(b)) => Ok(Some(Either::Right(b))),
            (None, None) => Ok(None),
        }
    }
}

pub struct EitherHomogeneous<A, B> {
    a: A,
    b: B,
}

impl<T, A, B> Arg for EitherHomogeneous<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<T>>,
{
    type Item = Option<T>;
    type Error = EitherError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        either_update_options(&self.a, &self.b, opts, notes);
    }
    fn name(&self) -> String {
        format!("({} or {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(EitherError::Left)?;
        let maybe_b = self.b.get(matches).map_err(EitherError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveArgs {
                left_name: self.a.name(),
                right_name: self.b.name(),
            }),
            (Some(a), None) => Ok(Some(a)),
            (None, Some(b)) => Ok(Some(b)),
            (None, None) => Ok(None),
        }
    }
}

pub struct WithDefault<P, T> {
    arg: P,
    default: T,
}

impl<P, T> Arg for WithDefault<P, T>
where
    T: Clone + Display,
    P: Arg<Item = Option<T>>,
{
    type Item = T;
    type Error = P::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        let note = Note::DefaultValue(format!("{}", self.default));
        self.arg.update_options(opts, notes.push(note));
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.arg
            .get(matches)?
            .unwrap_or_else(|| self.default.clone()))
    }
}

pub struct Required<P> {
    arg: P,
}

#[derive(Debug)]
pub enum RequiredError<E> {
    Other(E),
    MissingRequiredArg { name: String },
}

impl<E: Display> Display for RequiredError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            RequiredError::Other(e) => fmt::Display::fmt(&e, f),
            RequiredError::MissingRequiredArg { name } => {
                write!(f, "{} is required but not supplied", name)
            }
        }
    }
}

impl<P, T> Arg for Required<P>
where
    P: Arg<Item = Option<T>>,
{
    type Item = T;
    type Error = RequiredError<P::Error>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg
            .update_options(opts, notes.push(Note::Required));
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(RequiredError::Other)?
            .ok_or(RequiredError::MissingRequiredArg {
                name: self.arg.name(),
            })
    }
}

pub struct Convert<A, F> {
    arg: A,
    f: F,
}

#[derive(Debug)]
pub enum ConvertError<O, T, E> {
    Other(O),
    ConversionFailed { name: String, error: E, value: T },
}

impl<O: Display, T: Display, E: Display> Display for ConvertError<O, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ConvertError::Other(e) => fmt::Display::fmt(&e, f),
            ConvertError::ConversionFailed {
                name,
                error,
                value,
            } => write!(
                f,
                "invalid value \"{}\" supplied for \"{}\" ({})",
                value, name, error
            ),
        }
    }
}

impl<A, F, U, E> Arg for Convert<A, F>
where
    A: Arg,
    A::Item: Clone + Debug + Display,
    E: Debug + Display,
    F: Fn(&A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = ConvertError<A::Error, A::Item, E>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| {
                (self.f)(&o).map_err(|error| ConvertError::ConversionFailed {
                    name: self.arg.name(),
                    value: o,
                    error,
                })
            })
    }
}

pub struct OptConvert<A, F> {
    arg: A,
    f: F,
}

impl<T, A, U, F, E> Arg for OptConvert<A, F>
where
    T: Clone + Debug + Display,
    E: Clone + Debug + Display,
    A: Arg<Item = Option<T>>,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = ConvertError<A::Error, T, E>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| match o {
                Some(t) => (self.f)(t.clone()).map(Some).map_err(|error| {
                    ConvertError::ConversionFailed {
                        name: self.arg.name(),
                        value: t,
                        error,
                    }
                }),
                None => Ok(None),
            })
    }
}

pub struct Rename<P> {
    arg: P,
    name: String,
}

impl<P> Arg for Rename<P>
where
    P: Arg,
{
    type Item = P::Item;
    type Error = P::Error;

    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.name.clone()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches)
    }
}

pub struct AddNote<P> {
    arg: P,
    note: Note,
}

impl<P> Arg for AddNote<P>
where
    P: Arg,
{
    type Item = P::Item;
    type Error = P::Error;

    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.arg
            .update_options(opts, notes.push(self.note.clone()));
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches)
    }
}

pub struct SetNotesToDocument<P> {
    arg: P,
    which_notes_to_document: WhichNotes,
}

impl<P> Arg for SetNotesToDocument<P>
where
    P: Arg,
{
    type Item = P::Item;
    type Error = P::Error;

    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        let notes = Notes {
            which_notes_to_document: self.which_notes_to_document,
            ..notes
        };
        self.arg.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches)
    }
}

pub struct Value<T> {
    name: String,
    value: T,
}

impl<T> Arg for Value<T>
where
    T: Clone,
{
    type Item = T;
    type Error = Never;
    fn update_options(&self, _opts: &mut getopts::Options, _notes: Notes) {}
    fn name(&self) -> String {
        self.name.clone()
    }
    fn get(&self, _matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.value.clone())
    }
}

impl<T: Clone> Value<T> {
    pub fn new(value: T, name: &str) -> Value<T> {
        Self {
            value,
            name: name.to_string(),
        }
    }
}

pub trait ArgExt: Arg {
    fn map<U, F>(self, f: F) -> Map<Self, F>
    where
        F: Fn(Self::Item) -> U,
        Self: Sized,
    {
        Map { arg: self, f }
    }
    fn try_map<U, E, F>(self, f: F) -> TryMap<Self, F>
    where
        E: Debug,
        F: Fn(Self::Item) -> Result<U, E>,
        Self: Sized,
    {
        TryMap { arg: self, f }
    }
    fn join<B>(self, b: B) -> Join<Self, B>
    where
        B: Arg,
        Self: Sized,
    {
        Join { a: self, b }
    }
    fn convert<F, U, E>(self, f: F) -> Convert<Self, F>
    where
        E: Debug + Display,
        F: Fn(&Self::Item) -> Result<U, E>,
        Self: Sized,
        Self::Item: Clone + Debug,
    {
        Convert { arg: self, f }
    }
    fn rename(self, name: String) -> Rename<Self>
    where
        Self: Sized,
    {
        Rename { arg: self, name }
    }
    fn add_note(self, note: Note) -> AddNote<Self>
    where
        Self: Sized,
    {
        AddNote { arg: self, note }
    }
    fn set_notes_to_document(
        self,
        which_notes_to_document: WhichNotes,
    ) -> SetNotesToDocument<Self>
    where
        Self: Sized,
    {
        SetNotesToDocument {
            arg: self,
            which_notes_to_document,
        }
    }
    fn with_help(self, help: Flag) -> WithHelp<Self>
    where
        Self: Sized,
    {
        WithHelp {
            cond: help,
            value: self,
        }
    }
    fn with_default_help(self) -> WithHelp<Self>
    where
        Self: Sized,
    {
        self.with_help(Flag::default_help())
    }
}

impl<P: ?Sized> ArgExt for P
where
    P: Arg,
{
}

pub trait ArgOptionExt: Arg + ArgExt {
    type OptionItem;

    fn option_map<U, F>(self, f: F) -> OptionMap<Self, F>
    where
        F: Fn(Self::OptionItem) -> U,
        Self: Sized,
    {
        OptionMap { arg: self, f }
    }

    fn option_try_map<U, E, F>(self, f: F) -> OptionTryMap<Self, F>
    where
        E: Debug,
        F: Fn(Self::OptionItem) -> Result<U, E>,
        Self: Sized,
    {
        OptionTryMap { arg: self, f }
    }

    fn option_join<B>(self, b: B) -> OptionJoin<Self, B>
    where
        B: ArgOptionExt,
        Self: Sized,
    {
        OptionJoin { a: self, b }
    }

    fn either<B>(self, b: B) -> EitherCombinator<Self, B>
    where
        B: ArgOptionExt,
        Self: Sized,
    {
        EitherCombinator { a: self, b }
    }

    fn either_homogeneous<B>(self, b: B) -> EitherHomogeneous<Self, B>
    where
        B: ArgOptionExt<OptionItem = Self::OptionItem>,
        Self: Sized,
    {
        EitherHomogeneous { a: self, b }
    }

    fn with_default(
        self,
        default: Self::OptionItem,
    ) -> WithDefault<Self, Self::OptionItem>
    where
        Self: Sized,
    {
        WithDefault {
            arg: self,
            default,
        }
    }

    fn required(self) -> Required<Self>
    where
        Self: Sized,
    {
        Required { arg: self }
    }

    fn option_convert<F, U, E>(self, f: F) -> OptConvert<Self, F>
    where
        E: Debug + Display,
        F: Fn(Self::OptionItem) -> Result<U, E>,
        Self: Sized,
        Self::OptionItem: Clone + Debug,
    {
        OptConvert { arg: self, f }
    }

    fn otherwise<B>(self, b: B) -> Otherwise<Self, B>
    where
        B: Arg,
        Self: Sized,
    {
        Otherwise {
            cond: self,
            value: b,
        }
    }
}

impl<T, P: ?Sized> ArgOptionExt for P
where
    P: Arg<Item = Option<T>>,
{
    type OptionItem = T;
}

pub type UnitOption<T> = SomeIf<T, ()>;

pub trait ArgBoolExt: Arg + ArgExt {
    fn some_if<T>(self, value: T) -> SomeIf<Self, T>
    where
        Self: Sized,
    {
        SomeIf { arg: self, value }
    }
    fn unit_option(self) -> UnitOption<Self>
    where
        Self: Sized,
    {
        SomeIf {
            arg: self,
            value: (),
        }
    }
}

impl<P: ?Sized> ArgBoolExt for P
where
    P: Arg<Item = bool>,
{
}

pub fn value<T: Clone>(value: T, name: &str) -> impl Arg<Item = T, Error = Never> {
    Value::new(value, name)
}

pub fn flag(short: &str, long: &str, doc: &str) -> impl Arg<Item = bool, Error = Never> {
    Flag {
        short: short.to_string(),
        long: long.to_string(),
        doc: doc.to_string(),
    }
}

fn opt_str(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> impl Arg<Item = Option<String>> {
    Opt {
        short: short.to_string(),
        long: long.to_string(),
        doc: doc.to_string(),
        hint: hint.to_string(),
    }
}

pub fn opt_by<T, E, F>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    parse: F,
) -> impl Arg<Item = Option<T>>
where
    E: Clone + Debug + Display,
    F: Fn(String) -> Result<T, E>,
{
    opt_str(short, long, doc, hint).option_convert(parse)
}

pub fn opt_required_by<T, E, F>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    parse: F,
) -> impl Arg<Item = T>
where
    E: Clone + Debug + Display,
    F: Fn(String) -> Result<T, E>,
{
    opt_by(short, long, doc, hint, parse).required()
}

pub fn opt_default_by<T, E, F>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    default: T,
    parse: F,
) -> impl Arg<Item = T>
where
    E: Clone + Debug + Display,
    T: Clone + FromStr + Display,
    F: Fn(String) -> Result<T, E>,
{
    opt_by(short, long, doc, hint, parse).with_default(default)
}

pub fn opt<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> impl Arg<Item = Option<T>>
where
    T: FromStr,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    opt_by(short, long, doc, hint, |s| s.parse())
}

pub fn opt_required<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
) -> impl Arg<Item = T>
where
    T: FromStr,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    opt(short, long, doc, hint).required()
}

pub fn opt_default<T>(
    short: &str,
    long: &str,
    doc: &str,
    hint: &str,
    default: T,
) -> impl Arg<Item = T>
where
    T: Clone + FromStr + Display,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    opt(short, long, doc, hint).with_default(default)
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
macro_rules! join_args {
    ( $only:expr ) => {
        $only
    };
    ( $head:expr, $($tail:expr),* $(,)* ) => {
        $head $( .join($tail) )*
            .map(
                unflatten_closure!(a => (a) $(, $tail )*)
            )
    };
}

#[macro_export]
macro_rules! option_join_args {
    ( $only:expr ) => {
        $only
    };
    ( $head:expr, $($tail:expr),* $(,)* ) => {
        $head $( .option_join($tail) )*
            .option_map(
                unflatten_closure!(a => (a) $(, $tail )*)
            )
    };
}

#[macro_export]
macro_rules! map_args {
    ( let { $var1:ident = $a1:expr; } in { $b:expr } ) => {
        $a1.map(|$var1| $b)
    };
    ( let { $var1:ident = $a1:expr; $($var:ident = $a:expr;)+ } in { $b:expr } ) => {
        { join_args! {
            $a1, $($a),*
        } } .map(|($var1, $($var),*)| $b)
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::{Display, Write};

    fn string_fmt<D: Display>(d: &D) -> String {
        let mut s = String::new();
        write!(&mut s, "{}", d).unwrap();
        s
    }

    #[test]
    fn example() {
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum WindowSize {
            Dimensions { width: u32, height: u32 },
            FullScreen,
        }

        impl Display for WindowSize {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                match self {
                    WindowSize::Dimensions { width, height } => {
                        write!(f, "{}x{}", width, height)
                    }
                    WindowSize::FullScreen => write!(f, "fullscreen"),
                }
            }
        }

        #[derive(Debug, Clone, PartialEq, Eq)]
        struct Args {
            window_size: WindowSize,
            title: String,
        }

        let dimensions = opt("w", "width", "INT", "width")
            .option_join(opt("e", "height", "INT", "height"))
            .option_map(|(width, height)| WindowSize::Dimensions { width, height });

        let fullscreen =
            flag("f", "fullscreen", "fullscreen").some_if(WindowSize::FullScreen);

        let window_size = dimensions
            .either_homogeneous(fullscreen)
            .with_default(WindowSize::Dimensions {
                width: 640,
                height: 480,
            });

        let title = opt_required("t", "title", "STRING", "title");

        let arg = title
            .join(window_size)
            .map(|(title, window_size)| Args {
                title,
                window_size,
            });

        match arg.parse(&[""], Default::default()).0 {
            Err(e) => assert_eq!(string_fmt(&e), "title is required but not supplied"),
            Ok(o) => panic!("{:?}", o),
        }

        match arg
            .parse(&["--title", "foo", "--width", "potato"], Default::default())
            .0
        {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "invalid value \"potato\" supplied for \"width\" (invalid digit found in string)"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        match arg
            .parse(
                &[
                    "--title",
                    "foo",
                    "--width",
                    "4",
                    "--height",
                    "2",
                    "--fullscreen",
                ],
                Default::default(),
            )
            .0
        {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "(width and height) and fullscreen are mutually exclusive but both were supplied"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        match arg.parse(
            &["--title", "foo", "--width", "4", "--fullscreen"],
            Default::default(),
        ).0
        {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "width and height must be supplied together or not at all \
                 (width is supplied, height is missing)"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        assert_eq!(
            arg.parse(
                &["--title", "foo", "--fullscreen"],
                Default::default()
            ).0
                .unwrap(),
            Args {
                window_size: WindowSize::FullScreen,
                title: "foo".to_string(),
            }
        );

        assert_eq!(
            arg.parse(
                &["--title", "foo", "--width", "4", "--height", "2"],
                Default::default()
            ).0
                .unwrap(),
            Args {
                window_size: WindowSize::Dimensions {
                    width: 4,
                    height: 2,
                },
                title: "foo".to_string(),
            }
        );
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Args {
        foo: String,
        bar: i64,
        baz: (bool, bool),
        qux: Option<u32>,
    }

    #[test]
    fn map_args() {
        let arg = map_args! {
            let {
                foo = opt_required("f", "foo", "", "");
                bar = opt_required("b", "bar", "", "");
                baz = flag("l", "baz-left", "").join(flag("r", "baz-right", ""));
                qux = opt("q", "qux", "", "");
            } in {
                Args { foo, bar, baz, qux }
            }
        };

        let args = arg.parse(
            &[
                "--foo",
                "hello",
                "--bar",
                "12345",
                "--baz-right",
                "--qux",
                "42",
            ],
            Default::default(),
        ).0
            .unwrap();

        assert_eq!(
            args,
            Args {
                foo: "hello".to_string(),
                bar: 12345,
                baz: (false, true),
                qux: Some(42),
            }
        );
    }

    #[test]
    fn join_args() {
        let baz = flag("l", "baz-left", "").join(flag("r", "baz-right", ""));
        let arg = join_args! {
            opt_required("f", "foo", "", ""),
            opt_required("b", "bar", "", ""),
            baz,
            opt("q", "qux", "", ""),
        }.map(|(foo, bar, baz, qux)| Args {
            foo,
            bar,
            baz,
            qux,
        });

        let args = arg.parse(
            &[
                "--foo",
                "hello",
                "--bar",
                "12345",
                "--baz-right",
                "--qux",
                "42",
            ],
            Default::default(),
        ).0
            .unwrap();

        assert_eq!(
            args,
            Args {
                foo: "hello".to_string(),
                bar: 12345,
                baz: (false, true),
                qux: Some(42),
            }
        );
    }
}
