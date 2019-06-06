//! Envy is a library for deserializing environment variables into typesafe structs
//!
//! # Examples
//!
//! A typical usecase for envy is deserializing configuration store in an process' environment into a struct
//! whose fields map to the names of env vars.
//!
//! Serde makes it easy to provide a deserializable struct with its [deriveable Deserialize](https://serde.rs/derive.html)
//! procedural macro.
//!
//! Simply ask for an instance of that struct from envy's `from_map` function.
//!
//! ```no_run
//! use serde::Deserialize;
//! #[macro_use]
//! extern crate serde_derive;
//!
//! #[derive(Deserialize, Debug)]
//! struct Config {
//!   foo: u16,
//!   bar: bool,
//!   baz: String,
//!   boom: Option<u64>
//! }
//!
//! fn main() {
//!    match req2struct::from_map::<Config>() {
//!       Ok(config) => println!("{:#?}", config),
//!       Err(error) => panic!("{:#?}", error)
//!    }
//! }
//! ```
//!
//! Special treatment is given to collections. For config fields that store a `Vec` of values,
//! use and env var that uses a comma separated value
//!
//! All serde modifier should work as is
//!
//! If you wish to use enum types use the following
//!
//! ```no_run
//! use serde::Deserialize;
//! #[macro_use]
//! extern crate serde_derive;
//!
//! #[derive(Deserialize, Debug, PartialEq)]
//! #[serde(untagged)]
//! #[serde(field_identifier, rename_all = "lowercase")]
//! pub enum Size {
//!    Small,
//!    Medium,
//!    Large
//! }
//!
//! #[derive(Deserialize, Debug)]
//! struct Config {
//!  size: Size,
//! }
//!
//! fn main() {
//!    // set env var for size as `SIZE=medium`
//!    match req2struct::from_map::<Config>() {
//!       Ok(config) => println!("{:#?}", config),
//!       Err(error) => panic!("{:#?}", error)
//!    }
//! }
//! ```
//!

#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate log;
extern crate env_logger;

use serde::de::{
    self,
    value::{MapDeserializer, SeqDeserializer},
    IntoDeserializer,
};
use std::{borrow::Cow, collections::HashMap, iter::IntoIterator};

// Ours
mod error;
pub use crate::error::Error;

/// A type result type specific to `req2struct::Errors`
pub type Result<T> = std::result::Result<T, Error>;

struct Vars<Iter>(Iter)
where
    Iter: IntoIterator<Item = (String, FormFieldValue)>;

struct Val(String, FormFieldValue);

impl<'de> IntoDeserializer<'de, Error> for Val {
    type Deserializer = Self;

    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

struct VarName(String);

impl<'de> IntoDeserializer<'de, Error> for VarName {
    type Deserializer = Self;

    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

impl<Iter: Iterator<Item = (String, FormFieldValue)>> Iterator for Vars<Iter> {
    type Item = (VarName, Val);

    fn next(&mut self) -> Option<Self::Item> {
        println!("DESER NEXT");
        let the_next = self.0.next();
        println!("NEXT: {:#?}", &the_next);
        let ret = the_next.map(|(k, v)| {
            println!("k: {}", &k);
            /*
            let kv: Vec<&str> = k.split("__").collect();
            let kk = if kv.len() == 3 {
                kv[0].to_string().clone()
            } else {
                k.clone()
            };
            */
            let kk = k.clone();
            (VarName(kk.clone()), Val(kk, v))
        });
        ret
        // self.0.next().map(|(k, v)| (VarName(k.clone()), Val(k, v)))
    }
}

macro_rules! forward_parsed_values {
    ($($ty:ident => $method:ident,)*) => {
        $(
            fn $method<V>(self, visitor: V) -> Result<V::Value>
                where V: de::Visitor<'de>
            {
                println!("PPParsing: {:#?} {:#?}", &self.0, &self.1);
                match &self.1 {
                    FormFieldValue::Scalar(sclr) => {
                        // FIXME: later figure out how to deal with multiple values
                        match sclr.parse::<$ty>() {
                            Ok(val) => val.into_deserializer().$method(visitor),
                            Err(e) => Err(de::Error::custom(format_args!("{} while parsing value '{:#?}' provided by {}", e, self.1, self.0)))
                        }
                    },
                    FormFieldValue::Vector(vectr) => {
                        Err(de::Error::custom(format_args!("Vector seen rather than scalar while parsing value '{:#?}' provided by {}", self.1, self.0)))
                    }
                }
            }
        )*
    }
}

macro_rules! forward_parsed_values_scalar {
    ($($ty:ident => $method:ident,)*) => {
        $(
            fn $method<V>(self, visitor: V) -> Result<V::Value>
                where V: de::Visitor<'de>
            {
                println!("SCALAR PPParsing: {:#?}", &self);
                match &self {
                    FormFieldValue::Scalar(sclr) => {
                        // FIXME: later figure out how to deal with multiple values
                        match sclr.parse::<$ty>() {
                            Ok(val) => val.into_deserializer().$method(visitor),
                            Err(e) => Err(de::Error::custom(format_args!("{} while parsing value {:#?}", e, &self)))
                        }
                    },
                    FormFieldValue::Vector(vectr) => {
                        Err(de::Error::custom(format_args!("Vector seen rather than scalar while parsing value {:#?}", &self)))
                    }
                }
            }
        )*
    }
}

impl<'de> de::Deserializer<'de> for Val {
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        match self.1 {
            FormFieldValue::Scalar(sclr) => sclr.into_deserializer().deserialize_any(visitor),
            FormFieldValue::Vector(vectr) => {
                // FIXME
                // SeqDeserializer::new(vectr.into_iter()).deserialize_any(visitor) // .map(|m| from_iter(m.into_iter().deserialize_map(visitor))))
                Err(de::Error::custom(format_args!("ZZZZ unimpltemented!")))
            }
        }
    }

    // fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        // let values = self.1.split(',').map(|v| Val(self.0.clone(), v.to_owned()));
        // Err(de::Error::custom(format_args!("deserialize_seq unimpltemented!")))
        match self.1 {
            FormFieldValue::Scalar(s) => Err(de::Error::custom(format_args!(
                "Scalar in vector context: {} ",
                &self.0
            ))),
            FormFieldValue::Vector(vectr) => {
                MapDeserializer::new(Vars(vectr[0].clone().into_iter())).deserialize_map(visitor)

                // Err(de::Error::custom(format_args!( "deserialize_seq unimpltemented!")))
                // SeqDeserializer::new(vectr.into_iter().map(|x| x.into_iter()).deserialize_map(visitor)).deserialize_seq(visitor)
            }
        }
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        // Err(de::Error::custom(format_args!("deserialize_seq unimpltemented!")))
        match self.1 {
            FormFieldValue::Scalar(s) => Err(de::Error::custom(format_args!(
                "Scalar in vector context: {} ",
                &self.0
            ))),
            FormFieldValue::Vector(vectr) => {
                //let k: Vec<(String, String)> = vec![("Test1".to_string(), "Test2".to_string())];
                // SeqDeserializer::new(vectr.iter()).deserialize_seq(visitor)
                // SeqDeserializer::new(vectr.iter()).deserialize_seq(visitor)
                vectr.into_deserializer().deserialize_seq(visitor)
                // MapDeserializer::new(Vars(vectr[0].clone().into_iter())).deserialize_map(visitor)

                // SeqDeserializer::new(vectr.iter()).deserialize_seq(visitor)

                // Err(de::Error::custom(format_args!( "deserialize_seq unimpltemented!")))
                // SeqDeserializer::new(vectr.into_iter().map(|x| x.into_iter()).deserialize_map(visitor)).deserialize_seq(visitor)
            }
        }
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_some(self)
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        println!("Deserialize {:#?}", &self.1);
        let mut val = false;
        if let FormFieldValue::Scalar(sclr) = self.1 {
            if sclr == "on" {
                val = true;
            }
            if sclr == "true" {
                val = true;
            }
        }
        val.into_deserializer().deserialize_bool(visitor)
    }

    forward_parsed_values! {
        u8 => deserialize_u8,
        u16 => deserialize_u16,
        u32 => deserialize_u32,
        u64 => deserialize_u64,
        i8 => deserialize_i8,
        i16 => deserialize_i16,
        i32 => deserialize_i32,
        i64 => deserialize_i64,
        f32 => deserialize_f32,
        f64 => deserialize_f64,
    }

    #[inline]
    fn deserialize_newtype_struct<V>(self, _: &'static str, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        debug!("DESER newtype");
        visitor.visit_newtype_struct(self)
    }

    serde::forward_to_deserialize_any! {
        char str string unit
        bytes byte_buf unit_struct tuple_struct
        identifier tuple ignored_any enum
        struct
    }
}

impl<'de> de::Deserializer<'de> for VarName {
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        debug!("DESER ANY {:#?}", &self.0);
        self.0.into_deserializer().deserialize_any(visitor)
    }

    #[inline]
    fn deserialize_newtype_struct<V>(self, _: &'static str, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        debug!("DESER VISIT struct");
        visitor.visit_newtype_struct(self)
    }

    serde::forward_to_deserialize_any! {
        char str string unit seq option
        bytes byte_buf map unit_struct tuple_struct
        identifier tuple ignored_any enum
        struct bool u8 u16 u32 u64 i8 i16 i32 i64 f32 f64
    }
}

/// A deserializer for env vars
struct Deserializer<'de, Iter: Iterator<Item = (String, FormFieldValue)>> {
    inner: MapDeserializer<'de, Vars<Iter>, Error>,
}

impl<'de, Iter: Iterator<Item = (String, FormFieldValue)>> Deserializer<'de, Iter> {
    fn new(vars: Iter) -> Self {
        debug!("DESER new");
        Deserializer {
            inner: MapDeserializer::new(Vars(vars)),
        }
    }
}

impl<'de, Iter: Iterator<Item = (String, FormFieldValue)>> de::Deserializer<'de>
    for Deserializer<'de, Iter>
{
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        debug!("DESER Deserialize any!");
        self.deserialize_map(visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        debug!("DESER Deserialize map!");
        visitor.visit_map(self.inner)
    }

    serde::forward_to_deserialize_any! {
        bool u8 u16 u32 u64 i8 i16 i32 i64 f32 f64 char str string unit seq
        bytes byte_buf unit_struct tuple_struct
        identifier tuple ignored_any option newtype_struct enum
        struct
    }
}

/*

impl<'de, Iter: Iterator<Item = (HashMap<String, FormFieldValue>)>> de::Deserializer<'de>
    for Deserializer<'de, Iter>
{
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        println!("DESER Deserialize any!");
        self.deserialize_seq(visitor)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        println!("DESER Deserialize map!");
        visitor.visit_seq(self.inner)
    }

    serde::forward_to_deserialize_any! {
        bool u8 u16 u32 u64 i8 i16 i32 i64 f32 f64 char str string unit map
        bytes byte_buf unit_struct tuple_struct
        identifier tuple ignored_any option newtype_struct enum
        struct
    }
}

*/

#[derive(Debug, Clone, Deserialize)]
pub enum FormFieldValue {
    Scalar(String),
    Vector(Vec<HashMap<String, FormFieldValue>>),
}

impl<'de> IntoDeserializer<'de, Error> for FormFieldValue {
    type Deserializer = Self;

    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

impl<'de> de::Deserializer<'de> for FormFieldValue {
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        debug!("DESER FORMFIELD {:#?}", &self);
        match self {
            FormFieldValue::Scalar(s) => s.into_deserializer().deserialize_any(visitor),
            FormFieldValue::Vector(v) => v.into_deserializer().deserialize_any(visitor),
        }
    }

    forward_parsed_values_scalar! {
        u8 => deserialize_u8,
        u16 => deserialize_u16,
        u32 => deserialize_u32,
        u64 => deserialize_u64,
        i8 => deserialize_i8,
        i16 => deserialize_i16,
        i32 => deserialize_i32,
        i64 => deserialize_i64,
        f32 => deserialize_f32,
        f64 => deserialize_f64,
    }


    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        debug!("Deserialize BOOL FORMFIELD {:#?}", &self);
        let mut val = false;
        if let FormFieldValue::Scalar(s)  = self {
            if s== "on" {
                val = true;
            }
        }
        val.into_deserializer().deserialize_bool(visitor)
    }

    #[inline]
    fn deserialize_newtype_struct<V>(self, _: &'static str, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        debug!("DESER VISIT struct");
        visitor.visit_newtype_struct(self)
    }

    serde::forward_to_deserialize_any! {
        char str string unit seq option
        bytes byte_buf map unit_struct tuple_struct
        identifier tuple ignored_any enum
        struct // u8 u16 u32 u64 i8 i16 i32 i64 f32 f64
    }
}

fn map2vec(
    m: &HashMap<usize, HashMap<String, FormFieldValue>>,
) -> Vec<HashMap<String, FormFieldValue>> {
    let len = m.keys().len();
    let mut vo: Vec<HashMap<String, FormFieldValue>> = vec![];
    for i in 0..len {
        vo.push(m[&i].clone());
    }

    vo
}

/// Deserializes a type based on information stored in env variables
pub fn from_map<T>(m: &HashMap<String, Vec<String>>) -> Result<T>
where
    T: de::DeserializeOwned,
{
    debug!("DESER from map");
    let mut m1: HashMap<String, FormFieldValue> = m
        .clone()
        .iter()
        .filter(|(k, v)| {
            let vv: Vec<&str> = k.split("__").collect();
            vv.len() == 1
        })
        .map(|(k, v)| (k.to_owned(), FormFieldValue::Scalar(v[0].to_owned())))
        .collect();
    let mut m3: HashMap<String, FormFieldValue> = m
        .clone()
        .iter()
        .filter(|(k, v)| {
            let vv: Vec<&str> = k.split("__").collect();
            vv.len() == 3
        })
        .map(|(k, v)| {
            (
                k.clone(),
                // FormFieldValue::Scalar(format!("k = {}, v = {:?}", &k, &v)),
                FormFieldValue::Scalar(format!("{}", &v[0])),
            )
        })
        .collect();
    debug!("m1: {:#?}", &m1);
    debug!("m3: {:#?}", &m3);
    let mut m2: HashMap<String, HashMap<usize, HashMap<String, FormFieldValue>>> = HashMap::new();
    for (k, v) in m3 {
        let kk: Vec<&str> = k.split("__").collect();
        m2.entry(kk[0].to_string())
            .or_insert(HashMap::new())
            .entry(kk[1].to_string().parse::<usize>().unwrap_or(0))
            .or_insert(HashMap::new())
            .entry(kk[2].to_string())
            .or_insert(v);
    }

    let m4: HashMap<String, FormFieldValue> = m2
        .iter()
        .map(|(k, v)| (k.to_owned(), FormFieldValue::Vector(map2vec(v))))
        .collect();

    debug!("m2: {:#?}", &m2);
    debug!("m4: {:#?}", &m4);

    m1.extend(m4);

    from_iter(m1.iter().map(|(k, v)| {
        debug!("MAP {} - {:#?}", &k, &v);
        (k.to_string(), v.clone())
    }))
}

/// Deserializes a type based on an iterable of `(String, String)`
/// representing keys and values
pub fn from_iter<Iter, T>(iter: Iter) -> Result<T>
where
    T: de::DeserializeOwned,
    Iter: IntoIterator<Item = (String, FormFieldValue)>,
{
    debug!("DESER from iter");
    T::deserialize(Deserializer::new(iter.into_iter()))
}

/// A type which filters env vars with a prefix for use as serde field inputs
///
/// These types are created with with the [prefixed](fn.prefixed.html) module function
pub struct Prefixed<'a>(Cow<'a, str>);

impl<'a> Prefixed<'a> {
    /// Deserializes a type based on prefixed env varables
    pub fn from_map<T>(&self, m: &HashMap<String, FormFieldValue>) -> Result<T>
    where
        T: de::DeserializeOwned,
    {
        debug!("DESER from map2");
        self.from_iter(m.iter().map(|(k, v)| (k.to_string(), v.clone())))
    }

    /// Deserializes a type based on prefixed (String, String) tuples
    pub fn from_iter<Iter, T>(&self, iter: Iter) -> Result<T>
    where
        T: de::DeserializeOwned,
        Iter: IntoIterator<Item = (String, FormFieldValue)>,
    {
        debug!("DESER from iter2");
        crate::from_iter(iter.into_iter().filter_map(|(k, v)| {
            if k.starts_with(self.0.as_ref()) {
                Some((k.trim_start_matches(self.0.as_ref()).to_owned(), v))
            } else {
                None
            }
        }))
    }
}

/// Produces a instance of `Prefixed` for prefixing env variable names
///
/// # Example
///
/// ```no_run
/// use serde::Deserialize;
/// #[macro_use]
/// extern crate serde_derive;
///
/// #[derive(Deserialize, Debug)]
/// struct Config {
///   foo: u16,
///   bar: bool,
///   baz: String,
///   boom: Option<u64>
/// }
///
/// fn main() {
///    // all env variables will be expected to be prefixed with APP_
///    // i.e. APP_FOO, APP_BAR, ect
///    match req2struct::prefixed("APP_").from_map::<Config>() {
///       Ok(config) => println!("{:#?}", config),
///       Err(error) => panic!("{:#?}", error)
///    }
/// }
/// ```
pub fn prefixed<'a, C>(prefix: C) -> Prefixed<'a>
where
    C: Into<Cow<'a, str>>,
{
    Prefixed(prefix.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;
    use std::collections::HashMap;

    #[derive(Deserialize, Debug, PartialEq)]
    #[serde(untagged)]
    #[serde(field_identifier, rename_all = "lowercase")]
    pub enum Size {
        Small,
        Medium,
        Large,
    }

    impl Default for Size {
        fn default() -> Size {
            Size::Medium
        }
    }

    pub fn default_kaboom() -> u16 {
        8080
    }

    #[derive(Deserialize, Debug, PartialEq)]
    pub struct CustomNewType(u32);

    #[derive(Deserialize, Debug, PartialEq)]
    pub struct Foo {
        bar: String,
        baz: bool,
        zoom: Option<u16>,
        doom: Vec<u64>,
        #[serde(default = "default_kaboom")]
        kaboom: u16,
        #[serde(default)]
        debug_mode: bool,
        #[serde(default)]
        size: Size,
        provided: Option<String>,
        newtype: CustomNewType,
    }

    #[test]
    fn deserialize_from_iter() {
        let data = vec![
            (String::from("BAR"), String::from("test")),
            (String::from("BAZ"), String::from("true")),
            (String::from("DOOM"), String::from("1,2,3")),
            (String::from("SIZE"), String::from("small")),
            (String::from("PROVIDED"), String::from("test")),
            (String::from("NEWTYPE"), String::from("42")),
        ];
        match from_iter::<_, Foo>(data) {
            Ok(foo) => assert_eq!(
                foo,
                Foo {
                    bar: String::from("test"),
                    baz: true,
                    zoom: None,
                    doom: vec![1, 2, 3],
                    kaboom: 8080,
                    debug_mode: false,
                    size: Size::Small,
                    provided: Some(String::from("test")),
                    newtype: CustomNewType(42)
                }
            ),
            Err(e) => panic!("{:#?}", e),
        }
    }

    #[test]
    fn fails_with_missing_value() {
        let data = vec![
            (String::from("BAR"), String::from("test")),
            (String::from("BAZ"), String::from("true")),
        ];
        match from_iter::<_, Foo>(data) {
            Ok(_) => panic!("expected failure"),
            Err(e) => assert_eq!(e, Error::MissingValue("doom")),
        }
    }

    #[test]
    fn fails_with_invalid_type() {
        let data = vec![
            (String::from("BAR"), String::from("test")),
            (String::from("BAZ"), String::from("notabool")),
            (String::from("DOOM"), String::from("1,2,3")),
        ];
        match from_iter::<_, Foo>(data) {
            Ok(_) => panic!("expected failure"),
            Err(e) => assert_eq!(
                e,
                Error::Custom(String::from("provided string was not `true` or `false` while parsing value \'notabool\' provided by BAZ"))
            ),
        }
    }

    #[test]
    fn deserializes_from_prefixed_fieldnames() {
        let data = vec![
            (String::from("APP_BAR"), String::from("test")),
            (String::from("APP_BAZ"), String::from("true")),
            (String::from("APP_DOOM"), String::from("1,2,3")),
            (String::from("APP_SIZE"), String::from("small")),
            (String::from("APP_PROVIDED"), String::from("test")),
            (String::from("APP_NEWTYPE"), String::from("42")),
        ];
        match prefixed("APP_").from_iter::<_, Foo>(data) {
            Ok(foo) => assert_eq!(
                foo,
                Foo {
                    bar: String::from("test"),
                    baz: true,
                    zoom: None,
                    doom: vec![1, 2, 3],
                    kaboom: 8080,
                    debug_mode: false,
                    size: Size::Small,
                    provided: Some(String::from("test")),
                    newtype: CustomNewType(42)
                }
            ),
            Err(e) => panic!("{:#?}", e),
        }
    }

    #[test]
    fn prefixed_strips_prefixes() {
        let mut expected = HashMap::new();
        expected.insert("foo".to_string(), "bar".to_string());
        assert_eq!(
            prefixed("PRE_").from_iter(vec![("PRE_FOO".to_string(), "bar".to_string())]),
            Ok(expected)
        );
    }
}
