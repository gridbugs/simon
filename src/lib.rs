extern crate either;
extern crate getopts;

use std::str::FromStr;
use std::fmt::{self, Debug, Display, Write};
use std::ffi::OsStr;
use std::rc::Rc;

#[derive(Debug)]
pub enum TopLevelError<E> {
    Getopts(getopts::Fail),
    Other(E),
}

impl<E: Debug + Display> Display for TopLevelError<E> {
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

impl Default for WhichNotes {
    fn default() -> Self {
        Self {
            default_value: true,
            dependency: true,
            required: true,
        }
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
                write!(buf, "Default: {}", d);
            },
            Note::Dependency(c) => if which_notes.dependency {
                write!(buf, "Dependency: {}", c);
            },
            Note::Required => if which_notes.required {
                write!(buf, "Required");
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
                write!(buf, "{}", sep);
                node.0.append(which_notes, buf);
                node.1.append_rec(sep, which_notes, buf);
            }
        }
    }
}

impl Notes {
    fn new() -> Self {
        Self {
            list: NoteList::new(),
            which_notes_to_document: Default::default(),
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
                write!(buf, "(");
                node.0.append(self.which_notes_to_document, buf);
                node.1.append_rec(", ", self.which_notes_to_document, buf);
                write!(buf, ")");
            }
        }
    }
}

pub trait Param {
    type Item;
    type Error: Debug + Display;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes);
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error>;
    fn name(&self) -> String;
    fn parse<C: IntoIterator>(&self, args: C) -> Result<Self::Item, TopLevelError<Self::Error>>
    where
        C::Item: AsRef<OsStr>,
    {
        let mut opts = getopts::Options::new();
        self.update_options(&mut opts, Notes::new());
        self.get(&opts.parse(args)?).map_err(TopLevelError::Other)
    }
}

#[derive(Default)]
pub struct Arg {
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

#[derive(Debug)]
pub enum Never {}

impl Display for Never {
    fn fmt(&self, _f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            _ => unreachable!(),
        }
    }
}

impl Param for Arg {
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

impl Param for Flag {
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
    param: A,
    f: F,
}

impl<A, U, F> Param for Map<A, F>
where
    A: Param,
    F: Fn(A::Item) -> U,
{
    type Item = U;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param.get(matches).map(&self.f)
    }
}

pub struct SomeIf<A, T> {
    param: A,
    value: T,
}

impl<A, T> Param for SomeIf<A, T>
where
    T: Clone,
    A: Param<Item = bool>,
{
    type Item = Option<T>;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(if self.param.get(matches)? {
            Some(self.value.clone())
        } else {
            None
        })
    }
}

pub struct TryMap<A, F> {
    param: A,
    f: F,
}

#[derive(Debug)]
pub enum TryMapError<E, F> {
    Other(E),
    MapFailed(F),
}

impl<E: Debug + Display, F: Debug + Display> Display for TryMapError<E, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            TryMapError::MapFailed(fail) => fmt::Display::fmt(&fail, f),
            TryMapError::Other(other) => fmt::Display::fmt(&other, f),
        }
    }
}

impl<A, U, E, F> Param for TryMap<A, F>
where
    A: Param,
    E: Debug + Display,
    F: Fn(A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = TryMapError<A::Error, E>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(TryMapError::Other)
            .and_then(|o| (self.f)(o).map_err(TryMapError::MapFailed))
    }
}

pub struct OptMap<A, F> {
    param: A,
    f: F,
}

impl<A, T, U, F> Param for OptMap<A, F>
where
    A: Param<Item = Option<T>>,
    F: Fn(T) -> U,
{
    type Item = Option<U>;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param.get(matches).map(|v| v.map(&self.f))
    }
}

pub struct OptTryMap<A, F> {
    param: A,
    f: F,
}

impl<T, A, U, E, F> Param for OptTryMap<A, F>
where
    A: Param<Item = Option<T>>,
    E: Debug + Display,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = TryMapError<A::Error, E>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
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

pub type JoinError<A, B> = either::Either<A, B>;

impl<A, B> Param for Join<A, B>
where
    A: Param,
    B: Param,
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
            self.a.get(matches).map_err(either::Left)?,
            self.b.get(matches).map_err(either::Right)?,
        ))
    }
}

pub struct Codepend<A, B> {
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum CodependError<A, B> {
    Left(A),
    Right(B),
    MissingCodependantParam {
        supplied_name: String,
        missing_name: String,
    },
}

impl<A: Debug + Display, B: Debug + Display> Display for CodependError<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CodependError::Left(a) => fmt::Display::fmt(&a, f),
            CodependError::Right(b) => fmt::Display::fmt(&b, f),
            CodependError::MissingCodependantParam {
                supplied_name,
                missing_name,
            } => write!(
                f,
                "{} and {} must be supplied together or not at all ({} is supplied, {} is missing)",
                supplied_name, missing_name, supplied_name, missing_name
            ),
        }
    }
}

impl<T, U, A, B> Param for Codepend<A, B>
where
    A: Param<Item = Option<T>>,
    B: Param<Item = Option<U>>,
{
    type Item = Option<(T, U)>;
    type Error = CodependError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        let a_note = Note::Dependency(format!("must be specified with {}", self.b.name()));
        let b_note = Note::Dependency(format!("must be specified with {}", self.a.name()));
        self.a.update_options(opts, notes.clone().push(a_note));
        self.b.update_options(opts, notes.push(b_note));
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(CodependError::Left)?;
        let maybe_b = self.b.get(matches).map_err(CodependError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(a), Some(b)) => Ok(Some((a, b))),
            (None, None) => Ok(None),
            (Some(_), None) => Err(CodependError::MissingCodependantParam {
                supplied_name: self.a.name(),
                missing_name: self.b.name(),
            }),
            (None, Some(_)) => Err(CodependError::MissingCodependantParam {
                supplied_name: self.b.name(),
                missing_name: self.a.name(),
            }),
        }
    }
}

pub struct Either<A, B> {
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum EitherError<A, B> {
    Left(A),
    Right(B),
    MultipleMutuallyExclusiveParams {
        left_name: String,
        right_name: String,
    },
}

impl<A: Debug + Display, B: Debug + Display> Display for EitherError<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            EitherError::Left(a) => fmt::Display::fmt(&a, f),
            EitherError::Right(b) => fmt::Display::fmt(&b, f),
            EitherError::MultipleMutuallyExclusiveParams {
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
    a: &impl Param,
    b: &impl Param,
    opts: &mut getopts::Options,
    notes: Notes,
) {
    let a_note = Note::Dependency(format!("mutually exclusive with {}", b.name()));
    let b_note = Note::Dependency(format!("mutually exclusive with {}", a.name()));
    a.update_options(opts, notes.clone().push(a_note));
    b.update_options(opts, notes.push(b_note));
}

impl<T, U, A, B> Param for Either<A, B>
where
    A: Param<Item = Option<T>>,
    B: Param<Item = Option<U>>,
{
    type Item = Option<either::Either<T, U>>;
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
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveParams {
                left_name: self.a.name(),
                right_name: self.b.name(),
            }),
            (Some(a), None) => Ok(Some(either::Left(a))),
            (None, Some(b)) => Ok(Some(either::Right(b))),
            (None, None) => Ok(None),
        }
    }
}

pub struct EitherHomogeneous<A, B> {
    a: A,
    b: B,
}

impl<T, A, B> Param for EitherHomogeneous<A, B>
where
    A: Param<Item = Option<T>>,
    B: Param<Item = Option<T>>,
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
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveParams {
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
    param: P,
    default: T,
}

impl<P, T> Param for WithDefault<P, T>
where
    T: Clone + Display,
    P: Param<Item = Option<T>>,
{
    type Item = T;
    type Error = P::Error;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        let note = Note::DefaultValue(format!("{}", self.default));
        self.param.update_options(opts, notes.push(note));
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.param
            .get(matches)?
            .unwrap_or_else(|| self.default.clone()))
    }
}

pub struct Required<P> {
    param: P,
}

#[derive(Debug)]
pub enum RequiredError<E> {
    Other(E),
    MissingRequiredParam { name: String },
}

impl<E: Debug + Display> Display for RequiredError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            RequiredError::Other(e) => fmt::Display::fmt(&e, f),
            RequiredError::MissingRequiredParam { name } => {
                write!(f, "{} is required but not supplied", name)
            }
        }
    }
}

impl<P, T> Param for Required<P>
where
    P: Param<Item = Option<T>>,
{
    type Item = T;
    type Error = RequiredError<P::Error>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes.push(Note::Required));
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(RequiredError::Other)?
            .ok_or(RequiredError::MissingRequiredParam {
                name: self.param.name(),
            })
    }
}

pub struct Convert<A, F> {
    param: A,
    f: F,
}

#[derive(Debug)]
pub enum ConvertError<O, T, E> {
    Other(O),
    ConversionFailed { name: String, error: E, value: T },
}

impl<O: Debug + Display, T: Debug + Display, E: Debug + Display> Display for ConvertError<O, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ConvertError::Other(e) => fmt::Display::fmt(&e, f),
            ConvertError::ConversionFailed { name, error, value } => write!(
                f,
                "invalid value \"{}\" supplied for \"{}\" ({})",
                value, name, error
            ),
        }
    }
}

impl<A, F, U, E> Param for Convert<A, F>
where
    A: Param,
    A::Item: Clone + Debug + Display,
    E: Debug + Display,
    F: Fn(A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = ConvertError<A::Error, A::Item, E>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| {
                (self.f)(o.clone()).map_err(|error| ConvertError::ConversionFailed {
                    name: self.param.name(),
                    value: o,
                    error,
                })
            })
    }
}

pub struct OptConvert<A, F> {
    param: A,
    f: F,
}

impl<T, A, U, F, E> Param for OptConvert<A, F>
where
    T: Clone + Debug + Display,
    E: Clone + Debug + Display,
    A: Param<Item = Option<T>>,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = ConvertError<A::Error, T, E>;
    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| match o {
                Some(t) => (self.f)(t.clone()).map(Some).map_err(|error| {
                    ConvertError::ConversionFailed {
                        name: self.param.name(),
                        value: t,
                        error,
                    }
                }),
                None => Ok(None),
            })
    }
}

pub struct Rename<P> {
    param: P,
    name: String,
}

impl<P> Param for Rename<P>
where
    P: Param,
{
    type Item = P::Item;
    type Error = P::Error;

    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.name.clone()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param.get(matches)
    }
}

pub struct AddNote<P> {
    param: P,
    note: Note,
}

impl<P> Param for AddNote<P>
where
    P: Param,
{
    type Item = P::Item;
    type Error = P::Error;

    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        self.param
            .update_options(opts, notes.push(self.note.clone()));
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param.get(matches)
    }
}

pub struct SetNotesToDocument<P> {
    param: P,
    which_notes_to_document: WhichNotes,
}

impl<P> Param for SetNotesToDocument<P>
where
    P: Param,
{
    type Item = P::Item;
    type Error = P::Error;

    fn update_options(&self, opts: &mut getopts::Options, notes: Notes) {
        let notes = Notes {
            which_notes_to_document: self.which_notes_to_document,
            ..notes
        };
        self.param.update_options(opts, notes);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param.get(matches)
    }
}

pub trait ParamExt: Param {
    fn map<U, F>(self, f: F) -> Map<Self, F>
    where
        F: Fn(Self::Item) -> U,
        Self: Sized,
    {
        Map { param: self, f }
    }
    fn try_map<U, E, F>(self, f: F) -> TryMap<Self, F>
    where
        E: Debug,
        F: Fn(Self::Item) -> Result<U, E>,
        Self: Sized,
    {
        TryMap { param: self, f }
    }
    fn join<B>(self, b: B) -> Join<Self, B>
    where
        B: Param,
        Self: Sized,
    {
        Join { a: self, b }
    }
    fn convert<F, U, E>(self, f: F) -> Convert<Self, F>
    where
        E: Debug + Display,
        F: Fn(Self::Item) -> Result<U, E>,
        Self: Sized,
        Self::Item: Clone + Debug,
    {
        Convert { param: self, f }
    }
    fn rename(self, name: String) -> Rename<Self>
    where
        Self: Sized,
    {
        Rename { param: self, name }
    }
    fn add_note(self, note: Note) -> AddNote<Self>
    where
        Self: Sized,
    {
        AddNote { param: self, note }
    }
    fn set_notes_to_document(self, which_notes_to_document: WhichNotes) -> SetNotesToDocument<Self>
    where
        Self: Sized,
    {
        SetNotesToDocument {
            param: self,
            which_notes_to_document,
        }
    }
}

impl<P: ?Sized> ParamExt for P
where
    P: Param,
{
}

pub trait ParamOptExt: Param + ParamExt {
    type OptItem;

    fn opt_map<U, F>(self, f: F) -> OptMap<Self, F>
    where
        F: Fn(Self::OptItem) -> U,
        Self: Sized,
    {
        OptMap { param: self, f }
    }

    fn opt_try_map<U, E, F>(self, f: F) -> OptTryMap<Self, F>
    where
        E: Debug,
        F: Fn(Self::OptItem) -> Result<U, E>,
        Self: Sized,
    {
        OptTryMap { param: self, f }
    }

    fn codepend<B>(self, b: B) -> Codepend<Self, B>
    where
        B: ParamOptExt,
        Self: Sized,
    {
        Codepend { a: self, b }
    }

    fn either<B>(self, b: B) -> Either<Self, B>
    where
        B: ParamOptExt,
        Self: Sized,
    {
        Either { a: self, b }
    }

    fn either_homogeneous<B>(self, b: B) -> EitherHomogeneous<Self, B>
    where
        B: ParamOptExt<OptItem = Self::OptItem>,
        Self: Sized,
    {
        EitherHomogeneous { a: self, b }
    }

    fn with_default(self, default: Self::OptItem) -> WithDefault<Self, Self::OptItem>
    where
        Self: Sized,
    {
        WithDefault {
            param: self,
            default,
        }
    }

    fn required(self) -> Required<Self>
    where
        Self: Sized,
    {
        Required { param: self }
    }

    fn opt_convert<F, U, E>(self, f: F) -> OptConvert<Self, F>
    where
        E: Debug + Display,
        F: Fn(Self::OptItem) -> Result<U, E>,
        Self: Sized,
        Self::OptItem: Clone + Debug,
    {
        OptConvert { param: self, f }
    }
}

impl<T, P: ?Sized> ParamOptExt for P
where
    P: Param<Item = Option<T>>,
{
    type OptItem = T;
}

pub trait ParamBoolExt: Param + ParamExt {
    fn some_if<T>(self, value: T) -> SomeIf<Self, T>
    where
        Self: Sized,
    {
        SomeIf { param: self, value }
    }
}

impl<P: ?Sized> ParamBoolExt for P
where
    P: Param<Item = bool>,
{
}

pub fn flag(short: &str, long: &str, doc: &str) -> impl Param<Item = bool> {
    Flag {
        short: short.to_string(),
        long: long.to_string(),
        doc: doc.to_string(),
    }
}

fn arg_opt_str(
    short: &str,
    long: &str,
    hint: &str,
    doc: &str,
) -> impl Param<Item = Option<String>> {
    Arg {
        short: short.to_string(),
        long: long.to_string(),
        hint: hint.to_string(),
        doc: doc.to_string(),
    }
}

pub fn arg_opt<T>(short: &str, long: &str, hint: &str, doc: &str) -> impl Param<Item = Option<T>>
where
    T: FromStr,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    arg_opt_str(short, long, hint, doc).opt_convert(|s| s.parse())
}

pub fn arg_req<T>(short: &str, long: &str, hint: &str, doc: &str) -> impl Param<Item = T>
where
    T: FromStr,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    arg_opt(short, long, hint, doc).required()
}

pub fn arg_opt_def<T>(
    short: &str,
    long: &str,
    hint: &str,
    doc: &str,
    default: T,
) -> impl Param<Item = T>
where
    T: Clone + FromStr + Display,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    arg_opt(short, long, hint, doc).with_default(default)
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
macro_rules! join_params {
    ( $head:expr, $($tail:expr),* $(,)* ) => {{
        $head $( .join($tail) )*
            .map(
                unflatten_closure!(a => (a) $(, $tail )*)
            )
    }}
}

#[macro_export]
macro_rules! map_params {
    ( let { $($var:ident = $a:expr;)* } in { $b:expr } ) => {
        join_params! {
            $($a),*
        }.map(|($($var),*)| $b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::{Display, Write};

    fn string_fmt<D: Display>(d: &D) -> String {
        let mut s = String::new();
        write!(&mut s, "{}", d);
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
                    WindowSize::Dimensions { width, height } => write!(f, "{}x{}", width, height),
                    WindowSize::FullScreen => write!(f, "fullscreen"),
                }
            }
        }

        #[derive(Debug, Clone, PartialEq, Eq)]
        struct Args {
            window_size: WindowSize,
            title: String,
        }

        let dimensions = arg_opt("w", "width", "INT", "width")
            .codepend(arg_opt("e", "height", "INT", "height"))
            .opt_map(|(width, height)| WindowSize::Dimensions { width, height });

        let fullscreen = flag("f", "fullscreen", "fullscreen").some_if(WindowSize::FullScreen);

        let window_size = dimensions.either_homogeneous(fullscreen).with_default(
            WindowSize::Dimensions {
                width: 640,
                height: 480,
            },
        );

        let title = arg_req("t", "title", "STRING", "title");

        let param = title
            .join(window_size)
            .map(|(title, window_size)| Args { title, window_size });

        match param.parse(&[""]) {
            Err(e) => assert_eq!(string_fmt(&e), "title is required but not supplied"),
            Ok(o) => panic!("{:?}", o),
        }

        match param.parse(&["--title", "foo", "--width", "potato"]) {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "invalid value \"potato\" supplied for \"width\" (invalid digit found in string)"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        match param.parse(&[
            "--title",
            "foo",
            "--width",
            "4",
            "--height",
            "2",
            "--fullscreen",
        ]) {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "(width and height) and fullscreen are mutually exclusive but both were supplied"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        match param.parse(&["--title", "foo", "--width", "4", "--fullscreen"]) {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "width and height must be supplied together or not at all \
                 (width is supplied, height is missing)"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        assert_eq!(
            param.parse(&["--title", "foo", "--fullscreen"]).unwrap(),
            Args {
                window_size: WindowSize::FullScreen,
                title: "foo".to_string(),
            }
        );

        assert_eq!(
            param
                .parse(&["--title", "foo", "--width", "4", "--height", "2"])
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
    fn map_params() {
        let param = map_params! {
            let {
                foo = arg_req("f", "foo", "", "");
                bar = arg_req("b", "bar", "", "");
                baz = flag("l", "baz-left", "").join(flag("r", "baz-right", ""));
                qux = arg_opt("q", "qux", "", "");
            } in {
                Args { foo, bar, baz, qux }
            }
        };

        let args = param
            .parse(&[
                "--foo",
                "hello",
                "--bar",
                "12345",
                "--baz-right",
                "--qux",
                "42",
            ])
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
    fn join_params() {
        let baz = flag("l", "baz-left", "").join(flag("r", "baz-right", ""));
        let param = join_params! {
            arg_req("f", "foo", "", ""),
            arg_req("b", "bar", "", ""),
            baz,
            arg_opt("q", "qux", "", ""),
        }.map(|(foo, bar, baz, qux)| Args { foo, bar, baz, qux });

        let args = param
            .parse(&[
                "--foo",
                "hello",
                "--bar",
                "12345",
                "--baz-right",
                "--qux",
                "42",
            ])
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
