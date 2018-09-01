use getopts;
use std::ffi::OsStr;
use std::str::FromStr;
use std::marker::PhantomData;
use std::fmt::{Debug, Display};

#[derive(Debug)]
pub enum TopLevelError<E> {
    Getopts(getopts::Fail),
    Other(E),
}

impl<T> From<getopts::Fail> for TopLevelError<T> {
    fn from(f: getopts::Fail) -> Self {
        TopLevelError::Getopts(f)
    }
}

pub trait Param {
    type Item;
    type Error: Debug;
    fn update_options(&self, opts: &mut getopts::Options);
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error>;
    fn parse<C: IntoIterator>(&self, args: C) -> Result<Self::Item, TopLevelError<Self::Error>>
    where
        C::Item: AsRef<OsStr>,
    {
        let mut opts = getopts::Options::new();
        self.update_options(&mut opts);
        self.get(&opts.parse(args)?).map_err(TopLevelError::Other)
    }
}

pub struct Optional<T>(PhantomData<T>);
pub struct Required<T>(PhantomData<T>);
pub struct OptionalWithDefault<T> {
    default: T,
}

pub trait Occur {
    type Item;
    type Doc;
}

impl<T> Occur for Optional<T> {
    type Item = T;
    type Doc = String;
}
impl<T> Occur for Required<T> {
    type Item = T;
    type Doc = String;
}

pub type OptionalWithDefaultDoc<T> = Box<Fn(&T) -> String>;
impl<T> Occur for OptionalWithDefault<T> {
    type Item = T;
    type Doc = OptionalWithDefaultDoc<T>;
}
pub fn optional_with_default_doc<T, F>(f: F) -> OptionalWithDefaultDoc<T>
where
    F: 'static + Fn(&T) -> String,
{
    Box::new(f)
}
pub fn optional_with_default_doc_display<T: Display>(doc: &str) -> OptionalWithDefaultDoc<T> {
    let doc = doc.to_string();
    optional_with_default_doc(move |x| format!("{} {}", doc, x))
}
pub fn optional_with_default_doc_debug<T: Debug>(doc: &str) -> OptionalWithDefaultDoc<T> {
    let doc = doc.to_string();
    optional_with_default_doc(move |x| format!("{} {:?}", doc, x))
}

pub fn optional<T>() -> Optional<T> {
    Optional(PhantomData)
}

pub fn required<T>() -> Required<T> {
    Required(PhantomData)
}

pub fn optional_with_default<T>(default: T) -> OptionalWithDefault<T> {
    OptionalWithDefault { default }
}

pub struct ArgSpec<T, F: Fn(&str) -> Option<T>, O: Occur<Item = T>> {
    pub short: String,
    pub long: String,
    pub hint: String,
    pub doc: O::Doc,
    pub occur: O,
    pub convert: F,
}

pub fn default_convert<T: FromStr>(s: &str) -> Option<T> {
    s.parse().ok()
}

impl<T, F: Fn(&str) -> Option<T>, O: Occur<Item = T>> ArgSpec<T, F, O> {
    pub fn new(short: &str, long: &str, hint: &str, doc: O::Doc, occur: O, convert: F) -> Self {
        Self {
            short: short.to_string(),
            long: long.to_string(),
            hint: hint.to_string(),
            doc,
            occur,
            convert,
        }
    }
    fn convert(&self, string: &str) -> Option<T> {
        (self.convert)(string)
    }
}
impl<T: FromStr, O: Occur<Item = T>> ArgSpec<T, fn(&str) -> Option<T>, O> {
    pub fn new_from_str(short: &str, long: &str, hint: &str, doc: O::Doc, occur: O) -> Self {
        Self::new(short, long, hint, doc, occur, default_convert)
    }
}
impl<T, F: Fn(&str) -> Option<T>, O: Occur<Item = T, Doc = String>> ArgSpec<T, F, O> {
    fn doc(&self) -> String {
        self.doc.clone()
    }
}
impl<T, F: Fn(&str) -> Option<T>> ArgSpec<T, F, Required<T>> {
    pub fn new_required(short: &str, long: &str, hint: &str, doc: &str, convert: F) -> Self {
        Self::new(short, long, hint, doc.to_string(), required(), convert)
    }
}
impl<T, F: Fn(&str) -> Option<T>> ArgSpec<T, F, Optional<T>> {
    pub fn new_optional(short: &str, long: &str, hint: &str, doc: &str, convert: F) -> Self {
        Self::new(short, long, hint, doc.to_string(), optional(), convert)
    }
}
impl<T, F: Fn(&str) -> Option<T>> ArgSpec<T, F, OptionalWithDefault<T>> {
    pub fn new_optional_with_default<D>(
        short: &str,
        long: &str,
        hint: &str,
        doc: D,
        default: T,
        convert: F,
    ) -> Self
    where
        D: 'static + Fn(&T) -> String,
    {
        Self::new(
            short,
            long,
            hint,
            optional_with_default_doc(doc),
            optional_with_default(default),
            convert,
        )
    }
    fn doc(&self) -> String {
        (self.doc)(&self.occur.default)
    }
}
impl<T: FromStr> ArgSpec<T, fn(&str) -> Option<T>, Required<T>> {
    pub fn new_from_str_required(short: &str, long: &str, hint: &str, doc: &str) -> Self {
        Self::new_required(short, long, hint, doc, default_convert)
    }
}
impl<T: FromStr> ArgSpec<T, fn(&str) -> Option<T>, Optional<T>> {
    pub fn new_from_str_optional(short: &str, long: &str, hint: &str, doc: &str) -> Self {
        Self::new_optional(short, long, hint, doc, default_convert)
    }
}
impl<T: FromStr> ArgSpec<T, fn(&str) -> Option<T>, OptionalWithDefault<T>> {
    pub fn new_from_str_optional_with_default<D>(
        short: &str,
        long: &str,
        hint: &str,
        doc: D,
        default: T,
    ) -> Self
    where
        D: 'static + Fn(&T) -> String,
    {
        Self::new_optional_with_default(short, long, hint, doc, default, default_convert)
    }
}

#[derive(Debug)]
pub enum ArgError {
    FailedToParse {
        long: String,
        hint: String,
        value: String,
    },
}

impl<T, F: Fn(&str) -> Option<T>> Param for ArgSpec<T, F, Required<T>> {
    type Item = T;
    type Error = ArgError;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.reqopt(
            self.short.as_str(),
            self.long.as_str(),
            self.doc().as_str(),
            self.hint.as_str(),
        );
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let string = matches
            .opt_str(self.long.as_str())
            .expect("this should be caught by getopts::Options::parse");
        self.convert(string.as_str())
            .ok_or_else(|| ArgError::FailedToParse {
                long: self.long.clone(),
                hint: self.hint.clone(),
                value: string.clone(),
            })
    }
}

impl<T, F: Fn(&str) -> Option<T>> Param for ArgSpec<T, F, Optional<T>> {
    type Item = Option<T>;
    type Error = ArgError;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.optopt(
            self.short.as_str(),
            self.long.as_str(),
            self.doc().as_str(),
            self.hint.as_str(),
        );
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        match matches.opt_str(self.long.as_str()) {
            Some(string) => (self.convert)(string.as_str())
                .ok_or_else(|| ArgError::FailedToParse {
                    long: self.long.clone(),
                    hint: self.hint.clone(),
                    value: string.clone(),
                })
                .map(Some),
            None => Ok(None),
        }
    }
}

impl<T: Clone, F: Fn(&str) -> Option<T>> Param for ArgSpec<T, F, OptionalWithDefault<T>> {
    type Item = T;
    type Error = ArgError;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.optopt(
            self.short.as_str(),
            self.long.as_str(),
            self.doc().as_str(),
            self.hint.as_str(),
        );
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        match matches.opt_str(self.long.as_str()) {
            Some(string) => {
                (self.convert)(string.as_str()).ok_or_else(|| ArgError::FailedToParse {
                    long: self.long.clone(),
                    hint: self.hint.clone(),
                    value: string.clone(),
                })
            }
            None => Ok(self.occur.default.clone()),
        }
    }
}

pub struct Flag {
    long: String,
}

#[derive(Debug)]
pub enum Never {}

impl Param for Flag {
    type Item = bool;
    type Error = Never;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.optflag("", self.long.as_str(), "");
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_present(self.long.as_str()))
    }
}

pub fn flag(long: &str) -> impl Param<Item = bool> {
    Flag {
        long: long.to_string(),
    }
}
