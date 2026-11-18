//! A small JSON encoder used by the rustc driver.
//!
//! The rustc toolchain ships `serde` (rustc_public's data structures derive
//! `Serialize`) but does not ship a linkable `serde_json` library.  Keeping the
//! encoder here avoids another dependency and, more importantly, lets the
//! extractor use the approved rustc_public structures directly.  This module
//! does not parse text: it only serializes values supplied by the compiler API.

use serde::ser::{
    self, Serialize, SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant,
    SerializeTuple, SerializeTupleStruct, SerializeTupleVariant, Serializer,
};
use std::fmt::{self, Display};

#[derive(Debug)]
pub struct Error(pub String);

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

impl ser::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Self(msg.to_string())
    }
}

/// JSON values built by the encoder.
#[derive(Debug, Clone)]
pub enum Value {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Value>),
    Object(Vec<(String, Value)>),
}

impl Value {
    pub fn object(fields: impl IntoIterator<Item = (impl Into<String>, Value)>) -> Self {
        Self::Object(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
    }

    pub fn array(values: impl IntoIterator<Item = Value>) -> Self {
        Self::Array(values.into_iter().collect())
    }

    pub fn string(value: impl Into<String>) -> Self {
        Self::String(value.into())
    }

    pub fn number(value: impl ToString) -> Self {
        Self::Number(value.to_string())
    }

    pub fn write_to(&self, output: &mut String) {
        match self {
            Self::Null => output.push_str("null"),
            Self::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
            Self::Number(value) => output.push_str(value),
            Self::String(value) => {
                output.push('"');
                write_escaped(value, output);
                output.push('"');
            }
            Self::Array(values) => {
                output.push('[');
                for (index, value) in values.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    value.write_to(output);
                }
                output.push(']');
            }
            Self::Object(fields) => {
                output.push('{');
                for (index, (key, value)) in fields.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    output.push('"');
                    write_escaped(key, output);
                    output.push_str("\":");
                    value.write_to(output);
                }
                output.push('}');
            }
        }
    }
}

fn write_escaped(value: &str, output: &mut String) {
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                output.push_str(&format!("\\u{:04x}", character as u32));
            }
            character => output.push(character),
        }
    }
}

pub fn to_value<T: Serialize + ?Sized>(value: &T) -> Result<Value, Error> {
    value.serialize(JsonSerializer)
}

struct JsonSerializer;

struct Sequence {
    values: Vec<Value>,
    variant: Option<String>,
}

struct Structure {
    fields: Vec<(String, Value)>,
    variant: Option<String>,
}

struct Map {
    fields: Vec<(String, Value)>,
}

impl Sequence {
    fn finish(self) -> Result<Value, Error> {
        let value = Value::Array(self.values);
        Ok(match self.variant {
            Some(variant) => Value::object([(variant, value)]),
            None => value,
        })
    }
}

impl Structure {
    fn finish(self) -> Result<Value, Error> {
        let value = Value::Object(self.fields);
        Ok(match self.variant {
            Some(variant) => Value::object([(variant, value)]),
            None => value,
        })
    }
}

impl Map {
    fn finish(self) -> Result<Value, Error> {
        Ok(Value::Object(self.fields))
    }
}

impl SerializeSeq for Sequence {
    type Ok = Value;
    type Error = Error;

    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.values.push(value.serialize(JsonSerializer)?);
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        self.finish()
    }
}

impl SerializeTuple for Sequence {
    type Ok = Value;
    type Error = Error;

    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.values.push(value.serialize(JsonSerializer)?);
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        self.finish()
    }
}

impl SerializeTupleStruct for Sequence {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.values.push(value.serialize(JsonSerializer)?);
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        self.finish()
    }
}

impl SerializeTupleVariant for Sequence {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.values.push(value.serialize(JsonSerializer)?);
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        self.finish()
    }
}

impl SerializeStruct for Structure {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        self.fields.push((key.to_owned(), value.serialize(JsonSerializer)?));
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        self.finish()
    }
}

impl SerializeStructVariant for Structure {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        self.fields.push((key.to_owned(), value.serialize(JsonSerializer)?));
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        self.finish()
    }
}

impl SerializeMap for Map {
    type Ok = Value;
    type Error = Error;

    fn serialize_key<T: ?Sized + Serialize>(&mut self, key: &T) -> Result<(), Error> {
        self.fields.push((key.serialize(KeySerializer)?, Value::Null));
        Ok(())
    }

    fn serialize_value<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        let Some((_, slot)) = self.fields.last_mut() else {
            return Err(Error("map value appeared before its key".into()));
        };
        *slot = value.serialize(JsonSerializer)?;
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        self.finish()
    }
}

struct KeySerializer;

macro_rules! impossible_key {
    ($name:ident, $ty:ty) => {
        fn $name(self, _value: $ty) -> Result<String, Error> {
            Err(Error(format!("unsupported JSON map key: {}", stringify!($name))))
        }
    };
}

impl Serializer for KeySerializer {
    type Ok = String;
    type Error = Error;
    type SerializeSeq = ser::Impossible<String, Error>;
    type SerializeTuple = ser::Impossible<String, Error>;
    type SerializeTupleStruct = ser::Impossible<String, Error>;
    type SerializeTupleVariant = ser::Impossible<String, Error>;
    type SerializeMap = ser::Impossible<String, Error>;
    type SerializeStruct = ser::Impossible<String, Error>;
    type SerializeStructVariant = ser::Impossible<String, Error>;

    fn serialize_bool(self, value: bool) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_i8(self, value: i8) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_i16(self, value: i16) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_i32(self, value: i32) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_i64(self, value: i64) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_i128(self, value: i128) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_u8(self, value: u8) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_u16(self, value: u16) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_u32(self, value: u32) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_u64(self, value: u64) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_u128(self, value: u128) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_f32(self, value: f32) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_f64(self, value: f64) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_char(self, value: char) -> Result<String, Error> {
        Ok(value.to_string())
    }
    fn serialize_str(self, value: &str) -> Result<String, Error> {
        Ok(value.to_owned())
    }

    impossible_key!(serialize_bytes, &[u8]);
    fn serialize_none(self) -> Result<String, Error> {
        Err(Error("unsupported JSON map key: serialize_none".into()))
    }
    fn serialize_unit(self) -> Result<String, Error> {
        Err(Error("unsupported JSON map key: serialize_unit".into()))
    }

    fn serialize_some<T: ?Sized + Serialize>(self, _value: &T) -> Result<String, Error> {
        Err(Error("unsupported JSON map key: serialize_some".into()))
    }
    fn serialize_unit_struct(self, _name: &'static str) -> Result<String, Error> {
        Err(Error("unsupported JSON map key: serialize_unit_struct".into()))
    }
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Result<String, Error> {
        Ok(variant.to_owned())
    }
    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        _value: &T,
    ) -> Result<String, Error> {
        Err(Error("unsupported JSON map key: serialize_newtype_struct".into()))
    }
    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _value: &T,
    ) -> Result<String, Error> {
        Ok(variant.to_owned())
    }
    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Error> {
        Err(Error("unsupported JSON map key: sequence".into()))
    }
    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Error> {
        Err(Error("unsupported JSON map key: tuple".into()))
    }
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Error> {
        Err(Error("unsupported JSON map key: tuple struct".into()))
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Error> {
        Err(Error("unsupported JSON map key: tuple variant".into()))
    }
    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Error> {
        Err(Error("unsupported JSON map key: map".into()))
    }
    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Error> {
        Err(Error("unsupported JSON map key: struct".into()))
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Error> {
        Err(Error("unsupported JSON map key: struct variant".into()))
    }
}

impl Serializer for JsonSerializer {
    type Ok = Value;
    type Error = Error;
    type SerializeSeq = Sequence;
    type SerializeTuple = Sequence;
    type SerializeTupleStruct = Sequence;
    type SerializeTupleVariant = Sequence;
    type SerializeMap = Map;
    type SerializeStruct = Structure;
    type SerializeStructVariant = Structure;

    fn serialize_bool(self, value: bool) -> Result<Value, Error> {
        Ok(Value::Bool(value))
    }
    fn serialize_i8(self, value: i8) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_i16(self, value: i16) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_i32(self, value: i32) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_i64(self, value: i64) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_i128(self, value: i128) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_u8(self, value: u8) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_u16(self, value: u16) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_u32(self, value: u32) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_u64(self, value: u64) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_u128(self, value: u128) -> Result<Value, Error> {
        Ok(Value::number(value))
    }
    fn serialize_f32(self, value: f32) -> Result<Value, Error> {
        if value.is_finite() {
            Ok(Value::number(value))
        } else {
            Ok(Value::string(value.to_string()))
        }
    }
    fn serialize_f64(self, value: f64) -> Result<Value, Error> {
        if value.is_finite() {
            Ok(Value::number(value))
        } else {
            Ok(Value::string(value.to_string()))
        }
    }
    fn serialize_char(self, value: char) -> Result<Value, Error> {
        Ok(Value::string(value.to_string()))
    }
    fn serialize_str(self, value: &str) -> Result<Value, Error> {
        Ok(Value::string(value))
    }
    fn serialize_bytes(self, value: &[u8]) -> Result<Value, Error> {
        Ok(Value::array(value.iter().copied().map(Value::number)))
    }
    fn serialize_none(self) -> Result<Value, Error> {
        Ok(Value::Null)
    }
    fn serialize_some<T: ?Sized + Serialize>(self, value: &T) -> Result<Value, Error> {
        value.serialize(JsonSerializer)
    }
    fn serialize_unit(self) -> Result<Value, Error> {
        Ok(Value::Null)
    }
    fn serialize_unit_struct(self, _name: &'static str) -> Result<Value, Error> {
        Ok(Value::Null)
    }
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Result<Value, Error> {
        Ok(Value::string(variant))
    }
    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Value, Error> {
        value.serialize(JsonSerializer)
    }
    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Value, Error> {
        Ok(Value::object([(variant, value.serialize(JsonSerializer)?)]))
    }
    fn serialize_seq(self, _len: Option<usize>) -> Result<Sequence, Error> {
        Ok(Sequence { values: Vec::new(), variant: None })
    }
    fn serialize_tuple(self, _len: usize) -> Result<Sequence, Error> {
        self.serialize_seq(None)
    }
    fn serialize_tuple_struct(self, _name: &'static str, _len: usize) -> Result<Sequence, Error> {
        self.serialize_seq(None)
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Sequence, Error> {
        Ok(Sequence { values: Vec::new(), variant: Some(variant.to_owned()) })
    }
    fn serialize_map(self, _len: Option<usize>) -> Result<Map, Error> {
        Ok(Map { fields: Vec::new() })
    }
    fn serialize_struct(self, _name: &'static str, _len: usize) -> Result<Structure, Error> {
        Ok(Structure { fields: Vec::new(), variant: None })
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Structure, Error> {
        Ok(Structure { fields: Vec::new(), variant: Some(variant.to_owned()) })
    }
}
