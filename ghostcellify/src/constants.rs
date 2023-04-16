use crate::{
    lazy_static::lazy_static,
};

use std::{
    collections::{BTreeMap, HashMap},
    path::PathBuf,
    sync::{Mutex,},
};
use rustfix::Suggestion;
use rustc_span::{BytePos,};


lazy_static! {
    pub static ref REF_BORROW : String = "std::cell::RefCell::<T>::borrow".into();
    pub static ref REF_BORROW_MUT : String  = "std:cell::RefCell::<T>::borrow_mut".into();
}

lazy_static! {
    /// Rustfix suggestions for editing the source files
    ///
    /// File -> expression depth -> vec<suggestion>
    pub static ref RUSTFIX_SUGGESTIONS: Mutex<HashMap<PathBuf, BTreeMap<i32, Vec<Suggestion>>>> = Mutex::new(HashMap::default());
    /// Source code for each file
    pub static ref SOURCE_CODE: Mutex<HashMap<PathBuf, String>> = Mutex::new(HashMap::default());

    /// Buffer for compiler JSON diagnostic output
    pub static ref ERROR_BUFFER: Mutex<Vec<u8>> = Mutex::new(vec![]);

    /// The beginning position of the source file for the main crate
    pub static ref CRATE_FILE_POS: Mutex<Option<BytePos>> = Mutex::new(None);
}