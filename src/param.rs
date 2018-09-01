use getopts;
use std::ffi::OsStr;
use std::str::FromStr;

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
    type Error: ::std::fmt::Debug;
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

pub struct Optional;
pub struct Required;
pub struct OptionalWithDefault<T> {
    pub default: T,
}

pub trait Occur {}

impl Occur for Optional {}
impl Occur for Required {}
impl<T> Occur for OptionalWithDefault<T> {}

pub struct Single<T, F: Fn(&str) -> Option<T>, O: Occur> {
    long: String,
    convert: F,
    occur: O,
}

#[derive(Debug)]
pub enum SingleError {
    FailedToParse { long_flag: String, value: String },
}

impl<T, F: Fn(&str) -> Option<T>> Param for Single<T, F, Required> {
    type Item = T;
    type Error = SingleError;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.reqopt("", self.long.as_str(), "", "");
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let string = matches.opt_str(self.long.as_str()).unwrap();
        (self.convert)(string.as_str()).ok_or_else(|| SingleError::FailedToParse {
            long_flag: self.long.clone(),
            value: string.clone(),
        })
    }
}

impl<T: Clone, F: Fn(&str) -> Option<T>> Param for Single<T, F, OptionalWithDefault<T>> {
    type Item = T;
    type Error = SingleError;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.optopt("", self.long.as_str(), "", "");
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        match matches.opt_str(self.long.as_str()) {
            Some(string) => {
                (self.convert)(string.as_str()).ok_or_else(|| SingleError::FailedToParse {
                    long_flag: self.long.clone(),
                    value: string.clone(),
                })
            }
            None => Ok(self.occur.default.clone()),
        }
    }
}

impl<T, F: Fn(&str) -> Option<T>> Param for Single<T, F, Optional> {
    type Item = Option<T>;
    type Error = SingleError;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.optopt("", self.long.as_str(), "", "");
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        match matches.opt_str(self.long.as_str()) {
            Some(string) => (self.convert)(string.as_str())
                .ok_or_else(|| SingleError::FailedToParse {
                    long_flag: self.long.clone(),
                    value: string.clone(),
                })
                .map(Some),
            None => Ok(None),
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

pub fn param<T: FromStr, O: Occur>(
    long: &str,
    occur: O,
) -> Single<T, impl Fn(&str) -> Option<T>, O> {
    Single {
        long: long.to_string(),
        convert: |s| s.parse().ok(),
        occur,
    }
}

pub fn flag(long: &str) -> impl Param<Item = bool> {
    Flag {
        long: long.to_string(),
    }
}
