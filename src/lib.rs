#![no_std]

use core::{
    error::Error,
    fmt::{Display, Write},
    mem::take,
    ops::Deref,
};

use alloc::{
    borrow::ToOwned,
    boxed::Box,
    collections::{btree_map::BTreeMap, btree_set::BTreeSet},
    string::{String, ToString},
    vec::Vec,
};
use nom::{
    IResult, Parser,
    bytes::complete::tag,
    character::{
        complete::{alphanumeric0, space0},
        streaming::alphanumeric1,
    },
    error::{ErrorKind, FromExternalError},
    multi::many0,
    sequence::{delimited, terminated},
};
use pit_core::{Attr, parse_attr, parse_attrs, util::WriteUpdate};
extern crate alloc;
// #[cfg(feature = "unstable-to-pit")]
#[instability::unstable(feature = "to-pit")]
pub mod to_pit {
    include!("to_pit.rs");
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Sdk {
    pub interfaces: BTreeMap<String, SdkItem>,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SdkItem {
    pub generics: Arity,
    pub contents: SdkItemContents,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Arity {
    pub to_fill: BTreeMap<String, Arity>,
}
impl Display for Arity {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "<")?;
        for (a, b) in &self.to_fill {
            write!(f, "{a} {b}")?;
        }
        write!(f, ">")?;
        Ok(())
    }
}
impl Arity {
    pub fn parse(a: &str) -> IResult<&str, Self> {
        let (a, c) = space0
            .and_then(delimited(
                tag("<"),
                many0(space0.and_then((alphanumeric1, space0.and_then(Arity::parse)))),
                tag(">"),
            ))
            .parse(a)?;
        return Ok((
            a,
            Arity {
                to_fill: c.into_iter().map(|(a, b)| (a.to_owned(), b)).collect(),
            },
        ));
    }
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum SdkItemContents {
    Type(SdkParam),
    Method(SdkMethod),
}

pub trait Loader {
    type Error;
    fn load(
        &self,
        path: &str,
        closure: &mut (dyn FnMut(Result<&'_ Sdk, Self::Error>) -> Result<(), Self::Error> + '_),
    ) -> Result<(), Self::Error>;
}

pub trait Collector: Loader {
    fn collect_into(&self, a: &str, res: &mut BTreeSet<String>) -> Result<(), Self::Error> {
        if res.contains(a) {
            return Ok(());
        }
        res.insert(a.to_owned());
        return self.load(a, &mut |s| {
            let s = s?;
            return s.refs(&mut |a| self.collect_into(a, res));
        });
    }
    fn collect(&self, a: &str) -> Result<BTreeSet<String>, Self::Error> {
        let mut res = BTreeSet::default();
        self.collect_into(a, &mut res)?;
        Ok(res)
    }
    fn digest(&self, a: &str, d: &mut (dyn sha3::digest::Update + '_)) -> Result<(), Self::Error> {
        d.update(b"digest0");
        d.update(&[0xff]);
        d.update(a.as_bytes());
        d.update(&[0xff, 0xff]);
        let c = self.collect(a)?;
        for c in c.iter() {
            self.load(c.as_str(), &mut |s| {
                let s = match s {
                    Ok(s) => s,
                    Err(e) => return Err(e),
                };
                write!(WriteUpdate { wrapped: d }, "{c}").unwrap();
                d.update(&[0xff]);
                write!(WriteUpdate { wrapped: d }, "{s}").unwrap();
                d.update(&[0xff]);
                return Ok(());
            })?;
        }
        Ok(())
    }
}
impl<T: Loader + ?Sized> Collector for T {}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct SdkInterface {
    pub methods: BTreeMap<String, SdkMethod>,
    pub attr: Vec<Attr>,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct SdkMethod {
    pub args: BTreeMap<String, SdkParam>,
    pub rets: BTreeMap<String, SdkParam>,
    pub attr: Vec<Attr>,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SdkParam {
    pub ty: SdkTy,
    pub attr: Vec<Attr>,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum SdkTy {
    Generic {
        ty: String,
        args: BTreeMap<String, SdkParam>,
    },
    Path {
        sdk: Option<String>,
        ty: String,
        args: BTreeMap<String, SdkParam>,
    },
    I32,
    I64,
    F32,
    F64,
    Byte,
    I16,
    Array {
        item: Box<SdkParam>,
    },
    Struct {
        items: BTreeMap<String, SdkParam>,
    },
    Variant {
        choices: BTreeSet<SdkParam>,
    },
    Interface {
        implementation: SdkInterface,
    },
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct InstanceGenerics {
    pub value: BTreeMap<String, Instance>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Instance {
    pub ty: SdkParam,
    pub generics: InstanceGenerics,
}

impl Sdk {
    pub fn refs<E>(&self, next: &mut (dyn FnMut(&str) -> Result<(), E> + '_)) -> Result<(), E> {
        for x in self.interfaces.values() {
            match &x.contents {
                SdkItemContents::Type(sdk_param) => sdk_param.refs(next)?,
                SdkItemContents::Method(sdk_method) => {
                    for a in sdk_method.args.values().chain(sdk_method.rets.values()) {
                        a.refs(next)?;
                    }
                }
            }
        }
        Ok(())
    }
    pub fn parse(a: &str) -> IResult<&str, Self> {
        let (a, b) = many0((
            space0,
            alphanumeric0,
            space0,
            (
                Arity::parse,
                SdkParam::parse
                    .map(SdkItemContents::Type)
                    .or(SdkMethod::parse.map(SdkItemContents::Method)),
            )
                .map(|(a, b)| SdkItem {
                    generics: a,
                    contents: b,
                }),
        ))
        .parse(a)?;
        Ok((
            a,
            Self {
                interfaces: b
                    .into_iter()
                    .map(|(_, a, _, b)| (a.to_string(), b))
                    .collect(),
            },
        ))
    }
}
impl Display for Sdk {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for (a, b) in self.interfaces.iter() {
            write!(f, "{}", &b.generics)?;
            match &b.contents {
                SdkItemContents::Method(b) => write!(f, "{a} {b} ")?,
                SdkItemContents::Type(b) => write!(f, "{a} {b} ")?,
            }
        }
        Ok(())
    }
}
impl SdkParam {
    pub fn refs<E>(&self, next: &mut (dyn FnMut(&str) -> Result<(), E> + '_)) -> Result<(), E> {
        match &self.ty {
            SdkTy::Generic { args, .. } => {
                for v in args.values() {
                    v.refs(next)?;
                }
            }
            SdkTy::Path { args, sdk, .. } => {
                if let Some(sdk) = sdk.as_ref() {
                    next(sdk.as_str())?;
                }
                for v in args.values() {
                    v.refs(next)?;
                }
            }
            SdkTy::Array { item } => item.refs(next)?,
            SdkTy::Struct { items } => {
                for item in items.values() {
                    item.refs(next)?;
                }
            }
            SdkTy::Variant { choices } => {
                for item in choices {
                    item.refs(next)?;
                }
            }
            SdkTy::Interface { implementation } => {
                for val in implementation.methods.values() {
                    for item in val.args.values().chain(val.rets.values()) {
                        item.refs(next)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
    pub fn parse(a: &str) -> IResult<&str, Self> {
        let (a, attr) = parse_attrs(a)?;
        let (a, _) = space0(a)?;
        for (i, ty) in [
            ("i32", SdkTy::I32),
            ("i64", SdkTy::I64),
            ("f32", SdkTy::F32),
            ("f64", SdkTy::F64),
            ("byte", SdkTy::Byte),
            ("i8", SdkTy::Byte),
            ("i16", SdkTy::I16),
        ] {
            if let Some(a) = a.strip_prefix(i) {
                return Ok((a, Self { attr, ty }));
            }
        }

        if let Some(a) = a.strip_prefix("array") {
            // let (a, _) = space0(a)?;
            let (a, p) = SdkParam::parse(a)?;
            return Ok((
                a,
                Self {
                    attr,
                    ty: SdkTy::Array { item: Box::new(p) },
                },
            ));
        }

        if let Ok((a, x)) = delimited(
            tag("("),
            many0(terminated(
                (alphanumeric1, space0, SdkParam::parse),
                (space0, tag(",")),
            )),
            tag(")"),
        )
        .parse(a)
        {
            return Ok((
                a,
                Self {
                    attr,
                    ty: SdkTy::Struct {
                        items: x.into_iter().map(|(a, _, b)| (a.to_owned(), b)).collect(),
                    },
                },
            ));
        }

        if let Ok((a, x)) = delimited(
            tag("["),
            many0(terminated(SdkParam::parse, (space0, tag("|")))),
            tag("]"),
        )
        .parse(a)
        {
            return Ok((
                a,
                Self {
                    attr,
                    ty: SdkTy::Variant {
                        choices: x.into_iter().collect(),
                    },
                },
            ));
        }

        if let Ok((a, x)) = SdkInterface::parse(a) {
            return Ok((
                a,
                Self {
                    attr,
                    ty: SdkTy::Interface { implementation: x },
                },
            ));
        }

        if let Some(a) = a.strip_prefix("$") {
            if let Ok((a, s)) = space0::<&str, nom::error::Error<&str>>
                .and_then(alphanumeric0)
                .parse(a)
            {
                if let Ok((a, args)) = delimited(
                    tag("<"),
                    many0(terminated(
                        (space0.and_then(alphanumeric0), SdkParam::parse),
                        (space0, tag(",")),
                    )),
                    tag(">"),
                )
                .parse(a)
                {
                    return Ok((
                        a,
                        Self {
                            attr,
                            ty: SdkTy::Generic {
                                ty: s.to_string(),
                                args: args.into_iter().map(|(a, b)| (a.to_string(), b)).collect(),
                            },
                        },
                    ));
                }
            }
        }

        if let Ok((a, t)) = tag(":").and_then(space0).and_then(parse_attr).parse(a) {
            if let Ok((a, args)) = delimited(
                tag("<"),
                many0(terminated(
                    (space0.and_then(alphanumeric0), SdkParam::parse),
                    (space0, tag(",")),
                )),
                tag(">"),
            )
            .parse(a)
            {
                return Ok((
                    a,
                    Self {
                        attr,
                        ty: SdkTy::Path {
                            sdk: Some(t.value),
                            ty: t.name,
                            args: args.into_iter().map(|(a, b)| (a.to_string(), b)).collect(),
                        },
                    },
                ));
            };
        }

        if let Ok((a, n)) = alphanumeric0::<&str, nom::error::Error<&str>>(a) {
            if let Ok((a, args)) = delimited(
                tag("<"),
                many0(terminated(
                    (space0.and_then(alphanumeric0), SdkParam::parse),
                    (space0, tag(",")),
                )),
                tag(">"),
            )
            .parse(a)
            {
                return Ok((
                    a,
                    Self {
                        attr,
                        ty: SdkTy::Path {
                            sdk: None,
                            ty: n.to_string(),
                            args: args.into_iter().map(|(a, b)| (a.to_string(), b)).collect(),
                        },
                    },
                ));
            };
        }

        Err(nom::Err::Error(nom::error::Error::from_external_error(
            a,
            ErrorKind::Satisfy,
            "invalid type",
        )))
    }
}
impl Display for SdkParam {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for a in self.attr.iter() {
            write!(f, "{a} ")?;
        }
        match &self.ty {
            SdkTy::Generic { ty, args } => {
                write!(f, "${ty}<")?;
                let mut a = true;
                for (name, val) in args.iter() {
                    let a = take(&mut a);
                    if !a {
                        write!(f, ",")?;
                    }
                    write!(f, "{name} {val}")?;
                }
                write!(f, ">")?;
            }
            SdkTy::Path { sdk, ty, args } => {
                match sdk {
                    Some(a) => write!(f, ":[{ty}={a}]<")?,
                    None => write!(f, "{ty}<")?,
                };
                let mut a = true;
                for (name, val) in args.iter() {
                    let a = take(&mut a);
                    if !a {
                        write!(f, ",")?;
                    }
                    write!(f, "{name} {val}")?;
                }
                write!(f, ">")?;
            }
            SdkTy::I32 => write!(f, "i32")?,
            SdkTy::I64 => write!(f, "i64")?,
            SdkTy::F32 => write!(f, "f32")?,
            SdkTy::F64 => write!(f, "f64")?,
            SdkTy::Byte => write!(f, "byte")?,
            SdkTy::I16 => write!(f, "i16")?,
            SdkTy::Array { item } => write!(f, "array {item}")?,
            SdkTy::Struct { items } => {
                write!(f, "(")?;
                let mut a = true;
                for (k, item) in items.iter() {
                    let a = take(&mut a);
                    if !a {
                        write!(f, ",")?;
                    }
                    write!(f, " {k} {item} ")?;
                }
                write!(f, ")")?;
            }
            SdkTy::Variant { choices } => {
                write!(f, "[")?;
                let mut a = true;
                for item in choices.iter() {
                    let a = take(&mut a);
                    if !a {
                        write!(f, "|")?;
                    }
                    write!(f, " {item} ")?;
                }
                write!(f, "]")?;
            }
            SdkTy::Interface { implementation } => write!(f, "{implementation}")?,
        }
        Ok(())
    }
}
impl SdkInterface {
    pub fn parse(a: &str) -> IResult<&str, Self> {
        let (a, attr) = parse_attrs(a)?;
        let (a, _) = space0.and_then(tag("{")).parse(a)?;
        let (a, f) = space0
            .and_then(many0((space0.and_then(alphanumeric0), SdkMethod::parse)))
            .parse(a)?;
        let (a, _) = space0.and_then(tag("}")).parse(a)?;
        Ok((
            a,
            Self {
                methods: f.into_iter().map(|(a, b)| (a.to_string(), b)).collect(),
                attr,
            },
        ))
    }
}
impl Display for SdkInterface {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for a in self.attr.iter() {
            write!(f, " {a} ")?;
        }
        write!(f, "{}", "{")?;
        for (a, b) in self.methods.iter() {
            write!(f, " {a} {b} ")?;
        }
        write!(f, "{}", "}")?;
        Ok(())
    }
}
impl SdkMethod {
    pub fn parse(a: &str) -> IResult<&str, Self> {
        let (a, attr) = parse_attrs(a)?;
        let (a, _) = space0(a)?;
        let (a, p) = delimited(
            tag("("),
            many0(terminated(
                space0.and_then((alphanumeric0, SdkParam::parse)),
                space0.and_then(tag(",")),
            )),
            tag(")"),
        )
        .parse(a)?;
        let (a, _) = space0(a)?;
        let (a, _) = tag(":")(a)?;
        let (a, _) = space0(a)?;
        let (a, r) = delimited(
            tag("("),
            many0(terminated(
                space0.and_then((alphanumeric0, SdkParam::parse)),
                space0.and_then(tag(",")),
            )),
            tag(")"),
        )
        .parse(a)?;
        Ok((
            a,
            Self {
                args: p.into_iter().map(|(a, b)| (a.to_string(), b)).collect(),
                rets: r.into_iter().map(|(a, b)| (a.to_string(), b)).collect(),
                attr,
            },
        ))
    }
}
impl Display for SdkMethod {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for a in self.attr.iter() {
            write!(f, " {a} ")?;
        }
        write!(f, "(")?;
        let mut a = true;
        for (name, val) in self.args.iter() {
            let a = take(&mut a);
            if !a {
                write!(f, ",")?;
            }
            write!(f, "{name} {val}")?;
        }
        write!(f, "):(")?;
        let mut a = true;
        for (name, val) in self.rets.iter() {
            let a = take(&mut a);
            if !a {
                write!(f, ",")?;
            }
            write!(f, "{name} {val}")?;
        }
        write!(f, ")")?;
        Ok(())
    }
}
