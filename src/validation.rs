use crate::{SwitchCommon, SwitchShape, Switches};
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};

#[derive(PartialEq, Eq, Debug, Default)]
pub struct Invalid {
    pub duplicate_shorts: Vec<String>,
    pub duplicate_longs: Vec<String>,
    pub one_char_longs: Vec<String>,
    pub multi_char_shorts: Vec<String>,
    pub has_empty_switch: bool,
}

impl Invalid {
    fn new(
        duplicate_shorts: Vec<String>,
        duplicate_longs: Vec<String>,
        one_char_longs: Vec<String>,
        multi_char_shorts: Vec<String>,
        has_empty_switch: bool,
    ) -> Option<Self> {
        if duplicate_longs.is_empty()
            && duplicate_longs.is_empty()
            && one_char_longs.is_empty()
            && multi_char_shorts.is_empty()
            && !has_empty_switch
        {
            None
        } else {
            Some(Self {
                duplicate_shorts,
                duplicate_longs,
                one_char_longs,
                multi_char_shorts,
                has_empty_switch,
            })
        }
    }
}

impl Display for Invalid {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        assert!(
            !(self.duplicate_longs.is_empty()
                && self.duplicate_longs.is_empty()
                && self.one_char_longs.is_empty()
                && self.multi_char_shorts.is_empty()
                && !self.has_empty_switch)
        );

        write!(f, "Invalid argument spec!\n\n")?;
        if !self.duplicate_shorts.is_empty() {
            write!(f, "Duplicate shorts: \n{:#?}", self.duplicate_shorts)?;
        }
        if !self.duplicate_longs.is_empty() {
            write!(f, "Duplicate longs: \n{:#?}", self.duplicate_longs)?;
        }
        if !self.one_char_longs.is_empty() {
            write!(f, "Single-character longs: \n{:#?}", self.one_char_longs)?;
        }
        if !self.multi_char_shorts.is_empty() {
            write!(f, "Multi-character shorts: \n{:#?}", self.multi_char_shorts)?;
        }
        if self.has_empty_switch {
            write!(f, "Argument specified with neither short nor long switch")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SwitchInfo {
    common: SwitchCommon,
    arity: SwitchShape,
}

#[derive(Default)]
struct SwitchTable {
    table: HashMap<String, HashSet<SwitchInfo>>,
}

impl SwitchTable {
    fn insert(&mut self, key: &str, info: SwitchInfo) {
        self.table
            .entry(key.to_string())
            .or_insert_with(HashSet::default)
            .insert(info);
    }
    fn keys_with_multiple_values(&self) -> impl Iterator<Item = String> + '_ {
        self.table
            .iter()
            .filter_map(|(k, v)| if v.len() > 1 { Some(k.clone()) } else { None })
    }
}

#[derive(Default)]
struct InvalidNames {
    one_char_longs: Vec<String>,
    multi_char_shorts: Vec<String>,
    has_empty_switch: bool,
}

impl InvalidNames {
    fn insert(&mut self, info: &SwitchInfo) {
        let short = info.common.short.as_str();
        let long = info.common.long.as_str();
        if short.len() > 1 {
            self.multi_char_shorts.push(short.to_string());
        }
        if long.len() == 1 {
            self.one_char_longs.push(long.to_string());
        }
        if short.len() == 0 && long.len() == 0 {
            self.has_empty_switch = true;
        }
    }
}

#[derive(Default)]
struct Duplicates {
    by_short: SwitchTable,
    by_long: SwitchTable,
}

impl Duplicates {
    fn insert(&mut self, info: SwitchInfo) {
        let short = info.common.short.clone();
        let long = info.common.long.clone();
        if short.len() > 0 {
            self.by_short.insert(&short, info.clone());
        }
        if long.len() > 0 {
            self.by_long.insert(&long, info);
        }
    }
}

#[derive(Default)]
pub struct Checker {
    duplicates: Duplicates,
    invalid_names: InvalidNames,
}

impl Checker {
    fn insert(&mut self, info: SwitchInfo) {
        self.invalid_names.insert(&info);
        self.duplicates.insert(info);
    }
    pub fn invalid(self) -> Option<Invalid> {
        let Checker {
            duplicates: Duplicates { by_short, by_long },
            invalid_names:
                InvalidNames {
                    one_char_longs,
                    multi_char_shorts,
                    has_empty_switch,
                },
        } = self;
        let duplicate_shorts = by_short.keys_with_multiple_values().collect::<Vec<_>>();
        let duplicate_longs = by_long.keys_with_multiple_values().collect::<Vec<_>>();
        Invalid::new(
            duplicate_shorts,
            duplicate_longs,
            one_char_longs,
            multi_char_shorts,
            has_empty_switch,
        )
    }
}

impl Switches for Checker {
    fn add(&mut self, common: SwitchCommon, arity: SwitchShape) {
        self.insert(SwitchInfo { common, arity });
    }
}
