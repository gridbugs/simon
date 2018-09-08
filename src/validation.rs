use std::fmt::{self, Display};

#[derive(Debug)]
pub struct Invalid {
    duplicate_longs: Vec<String>,
    duplicate_shorts: Vec<String>,
    one_char_longs: Vec<String>,
    multi_char_shorts: Vec<String>,
}

impl Display for Invalid {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if !(self.duplicate_longs.is_empty() && self.duplicate_shorts.is_empty()
            && self.one_char_longs.is_empty()
            && self.multi_char_shorts.is_empty())
        {
            write!(f, "Invalid argument spec!\n\n")?;
        }
        if !self.duplicate_longs.is_empty() {
            write!(f, "Duplicate longs: \n{:#?}", self.duplicate_longs)?;
        }
        if !self.duplicate_shorts.is_empty() {
            write!(f, "Duplicate shorts: \n{:#?}", self.duplicate_shorts)?;
        }
        if !self.one_char_longs.is_empty() {
            write!(f, "Single-character longs: \n{:#?}", self.one_char_longs)?;
        }
        if !self.multi_char_shorts.is_empty() {
            write!(f, "Multi-character shorts: \n{:#?}", self.multi_char_shorts)?;
        }
        Ok(())
    }
}
