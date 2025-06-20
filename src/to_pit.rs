use core::{error::Error, fmt::Formatter};

use alloc::{format, vec};
use itertools::Itertools;
use pit_core::{
    Arg, Interface, Sig,
    info::{Info, InfoEntry, MethEntry},
};

use crate::*;
fn dfn<T: FnMut(&mut Formatter) -> core::fmt::Result>(t: T) -> impl Display {
    struct I<T>(pub spin::Mutex<T>);
    impl<T: FnMut(&mut Formatter) -> core::fmt::Result> Display for I<T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
            let mut lock = self.0.lock();
            (lock)(f)
        }
    }

    return I(spin::Mutex::new(t));
}
pub trait Store {
    type Error: Error;
    fn store(&mut self, a: &Interface) -> Result<(), Self::Error>;
}
pub trait ToPitTy {
    fn to_pit<Error: core::error::Error>(
        &self,
        store: &mut (dyn Store<Error = Error> + '_),
        load: &(dyn Loader<Error = Error> + '_),
        info: &mut Info,
        arity: &Arity,
        path: &(dyn Display + '_),
        via: &mut (dyn FnMut(pit_core::Arg, &[Attr]) -> Result<(), Error> + '_),
    ) -> Result<(), Error>;
    fn to_pit_generic<Error: core::error::Error>(
        &self,
        store: &mut (dyn Store<Error = Error> + '_),
        load: &(dyn Loader<Error = Error> + '_),
        info: &mut Info,
        arity: &Arity,
        path: &(dyn Display + '_),
        // fmt: &mut Formatter,
    ) -> Result<String, Error>;
}
fn render_arity(a: &Arity) -> String {
    format!(
        "{}",
        a.to_fill
            .iter()
            .map(|(a, b)| format!("P{a};{}", render_arity(b)))
            .join(";")
    )
}
fn splat_arity(a: &Arity) -> String {
    format!(
        "{}",
        a.to_fill
            .iter()
            .map(|(a, b)| format!("F{a};P{a}"))
            .join(";")
    )
}
impl ToPitTy for SdkParam {
    fn to_pit<Error: pit_core::util::core::error::Error>(
        &self,
        store: &mut (dyn Store<Error = Error> + '_),
        load: &(dyn Loader<Error = Error> + '_),
        info: &mut Info,
        arity: &Arity,
        path: &(dyn Display + '_),
        via: &mut (dyn FnMut(pit_core::Arg, &[Attr]) -> Result<(), Error> + '_),
    ) -> Result<(), Error> {
        let attr = self.attr.clone();
        match &self.ty {
            SdkTy::Generic { ty, args } => via(
                Arg::Resource {
                    ty: pit_core::ResTy::None,
                    nullable: true,
                    take: false,
                    ann: attr
                        .into_iter()
                        .chain([Attr {
                            name: format!("generics"),
                            value: format!(
                                "P{ty};{}",
                                args.iter()
                                    .map(|(a, b)| Ok(format!(
                                        "F{a};{}",
                                        b.to_pit_generic(store, load, info, arity, path)?
                                    )))
                                    .collect::<Result<Vec<_>, Error>>()?
                                    .into_iter()
                                    .join(";")
                            ),
                        }])
                        .collect(),
                },
                &[],
            ),
            SdkTy::Path { sdk, ty, args } => todo!(),
            SdkTy::I32 => todo!(),
            SdkTy::I64 => todo!(),
            SdkTy::F32 => todo!(),
            SdkTy::F64 => todo!(),
            SdkTy::Byte => todo!(),
            SdkTy::I16 => todo!(),
            SdkTy::Array { item } => todo!(),
            SdkTy::Struct { items } => {
                let mut snap = InfoEntry::default();
                let methods = items
                    .iter()
                    .map(|(k, v)| {
                        Ok((
                            k.to_owned(),
                            Sig {
                                ann: vec![],
                                params: vec![],
                                rets: {
                                    let mut s = Vec::default();
                                    // for a in v.rets.values() {
                                    v.to_pit(
                                        store,
                                        load,
                                        info,
                                        arity,
                                        &format_args!("{path}.sf_{k}"),
                                        &mut |x, y| {
                                            let x2 =
                                                take(snap.methods.entry(k.to_owned()).or_default());
                                            *snap.methods.entry(k.to_owned()).or_default() = x2
                                                .merge(MethEntry {
                                                    attrs: y
                                                        .iter()
                                                        .map(|Attr { name, value }| Attr {
                                                            name: format!("{}.{name}", s.len()),
                                                            value: value.clone(),
                                                        })
                                                        .collect(),
                                                });
                                            Ok(s.push(x))
                                        },
                                    )?;
                                    // }
                                    s
                                },
                            },
                        ))
                    })
                    .collect::<Result<BTreeMap<_, _>, Error>>()?;
                let i = Interface {
                    methods,
                    ann: []
                        .into_iter()
                        .chain([
                            Attr {
                                name: format!("generic_params"),
                                value: render_arity(arity),
                            },
                            Attr {
                                name: format!("sdk.root_path"),
                                value: format!("{path}"),
                            },
                        ])
                        .collect(),
                };
                store.store(&i)?;
                *info.interfaces.entry(i.rid()).or_default() =
                    take(info.interfaces.entry(i.rid()).or_default()).merge(snap);
                via(
                    Arg::Resource {
                        ty: pit_core::ResTy::Of(i.rid()),
                        nullable: true,
                        take: false,
                        ann: attr
                            .into_iter()
                            .chain([Attr {
                                name: format!("generics"),
                                value: splat_arity(arity),
                            }])
                            .collect(),
                    },
                    &[],
                )
            }
            SdkTy::Variant { choices } => todo!(),
            SdkTy::Interface { implementation } => {
                let mut snap = InfoEntry::default();
                let methods = implementation
                    .methods
                    .iter()
                    .map(|(k, v)| {
                        Ok((
                            k.to_owned(),
                            Sig {
                                ann: v.attr.clone(),
                                params: {
                                    let mut s = Vec::default();
                                    for (ak, a) in v.args.iter() {
                                        a.to_pit(
                                            store,
                                            load,
                                            info,
                                            arity,
                                            &format_args!("{path}.ika_{k}_{ak}"),
                                            &mut |x, y| {
                                                let x2 = take(
                                                    snap.methods.entry(k.to_owned()).or_default(),
                                                );
                                                *snap.methods.entry(k.to_owned()).or_default() = x2
                                                    .merge(MethEntry {
                                                        attrs: y
                                                            .iter()
                                                            .map(|Attr { name, value }| Attr {
                                                                name: format!(
                                                                    "a{}.{name}",
                                                                    s.len()
                                                                ),
                                                                value: value.clone(),
                                                            })
                                                            .collect(),
                                                    });
                                                Ok(s.push(x))
                                            },
                                        )?;
                                    }
                                    s
                                },
                                rets: {
                                    let mut s = Vec::default();
                                    for (ak, a) in v.args.iter() {
                                        a.to_pit(
                                            store,
                                            load,
                                            info,
                                            arity,
                                            &format_args!("{path}.ikr_{k}_{ak}"),
                                            &mut |x, y| {
                                                *snap.methods.entry(k.to_owned()).or_default() =
                                                    take(
                                                        snap.methods
                                                            .entry(k.to_owned())
                                                            .or_default(),
                                                    )
                                                    .merge(MethEntry {
                                                        attrs: y
                                                            .iter()
                                                            .map(|Attr { name, value }| Attr {
                                                                name: format!(
                                                                    "r{}.{name}",
                                                                    s.len()
                                                                ),
                                                                value: value.clone(),
                                                            })
                                                            .collect(),
                                                    });
                                                Ok(s.push(x))
                                            },
                                        )?;
                                    }
                                    s
                                },
                            },
                        ))
                    })
                    .collect::<Result<BTreeMap<_, _>, Error>>()?;
                let i = Interface {
                    methods,
                    ann: implementation
                        .attr
                        .clone()
                        .into_iter()
                        .chain([
                            Attr {
                                name: format!("generic_params"),
                                value: render_arity(arity),
                            },
                            Attr {
                                name: format!("sdk.root_path"),
                                value: format!("{path}"),
                            },
                        ])
                        .collect(),
                };
                store.store(&i)?;
                *info.interfaces.entry(i.rid()).or_default() =
                    take(info.interfaces.entry(i.rid()).or_default()).merge(snap);
                via(
                    Arg::Resource {
                        ty: pit_core::ResTy::Of(i.rid()),
                        nullable: true,
                        take: false,
                        ann: attr
                            .into_iter()
                            .chain([Attr {
                                name: format!("generics"),
                                value: splat_arity(arity),
                            }])
                            .collect(),
                    },
                    &[],
                )
            }
        }
    }

    fn to_pit_generic<Error: pit_core::util::core::error::Error>(
        &self,
        store: &mut (dyn Store<Error = Error> + '_),
        load: &(dyn Loader<Error = Error> + '_),
        info: &mut Info,
        arity: &Arity,
        path: &(dyn Display + '_),
        // fmt: &mut Formatter,
    ) -> Result<String, Error> {
        Ok(match &self.ty {
            SdkTy::Generic { ty, args } => format!(
                "P{ty};{}",
                args.iter()
                    .map(|(a, b)| Ok(format!(
                        "F{a};{}",
                        b.to_pit_generic(store, load, info, arity, path)?
                    )))
                    .collect::<Result<Vec<_>, Error>>()?
                    .into_iter()
                    .join(";")
            ),
            SdkTy::Path { sdk, ty, args } => todo!(),
            SdkTy::I32 => todo!(),
            SdkTy::I64 => todo!(),
            SdkTy::F32 => todo!(),
            SdkTy::F64 => todo!(),
            SdkTy::Byte => todo!(),
            SdkTy::I16 => todo!(),
            SdkTy::Array { item } => todo!(),
            SdkTy::Struct { items } => {
                let mut snap = InfoEntry::default();
                let methods = items
                    .iter()
                    .map(|(k, v)| {
                        Ok((
                            k.to_owned(),
                            Sig {
                                ann: vec![],
                                params: vec![],
                                rets: {
                                    let mut s = Vec::default();
                                    // for a in v.rets.values() {
                                    v.to_pit(
                                        store,
                                        load,
                                        info,
                                        arity,
                                        &format_args!("{path}.sf_{k}"),
                                        &mut |x, y| {
                                            let x2 =
                                                take(snap.methods.entry(k.to_owned()).or_default());
                                            *snap.methods.entry(k.to_owned()).or_default() = x2
                                                .merge(MethEntry {
                                                    attrs: y
                                                        .iter()
                                                        .map(|Attr { name, value }| Attr {
                                                            name: format!("{}.{name}", s.len()),
                                                            value: value.clone(),
                                                        })
                                                        .collect(),
                                                });
                                            Ok(s.push(x))
                                        },
                                    )?;
                                    // }
                                    s
                                },
                            },
                        ))
                    })
                    .collect::<Result<BTreeMap<_, _>, Error>>()?;
                let i = Interface {
                    methods,
                    ann: []
                        .into_iter()
                        .chain([
                            Attr {
                                name: format!("generic_params"),
                                value: render_arity(arity),
                            },
                            Attr {
                                name: format!("sdk.root_path"),
                                value: format!("{path}"),
                            },
                        ])
                        .collect(),
                };
                store.store(&i)?;
                // info.interfaces.entry(i.rid()).or_default().merge(snap);
                *info.interfaces.entry(i.rid()).or_default() =
                    take(info.interfaces.entry(i.rid()).or_default()).merge(snap);
                format!("R{};{}", i.rid_str(), splat_arity(arity))
            }
            SdkTy::Variant { choices } => todo!(),
            SdkTy::Interface { implementation } => {
                let mut snap = InfoEntry::default();
                let methods = implementation
                    .methods
                    .iter()
                    .map(|(k, v)| {
                        Ok((
                            k.to_owned(),
                            Sig {
                                ann: v.attr.clone(),
                                params: {
                                    let mut s = Vec::default();
                                    for (ak, a) in v.args.iter() {
                                        a.to_pit(
                                            store,
                                            load,
                                            info,
                                            arity,
                                            &format_args!("{path}.ika_{k}_{ak}"),
                                            &mut |x, y| {
                                                let x2 = take(
                                                    snap.methods.entry(k.to_owned()).or_default(),
                                                );
                                                *snap.methods.entry(k.to_owned()).or_default() = x2
                                                    .merge(MethEntry {
                                                        attrs: y
                                                            .iter()
                                                            .map(|Attr { name, value }| Attr {
                                                                name: format!(
                                                                    "a{}.{name}",
                                                                    s.len()
                                                                ),
                                                                value: value.clone(),
                                                            })
                                                            .collect(),
                                                    });
                                                Ok(s.push(x))
                                            },
                                        )?;
                                    }
                                    s
                                },
                                rets: {
                                    let mut s = Vec::default();
                                    for (ak, a) in v.args.iter() {
                                        a.to_pit(
                                            store,
                                            load,
                                            info,
                                            arity,
                                            &format_args!("{path}.ikr_{k}_{ak}"),
                                            &mut |x, y| {
                                                *snap.methods.entry(k.to_owned()).or_default() =
                                                    take(
                                                        snap.methods
                                                            .entry(k.to_owned())
                                                            .or_default(),
                                                    )
                                                    .merge(MethEntry {
                                                        attrs: y
                                                            .iter()
                                                            .map(|Attr { name, value }| Attr {
                                                                name: format!(
                                                                    "r{}.{name}",
                                                                    s.len()
                                                                ),
                                                                value: value.clone(),
                                                            })
                                                            .collect(),
                                                    });
                                                Ok(s.push(x))
                                            },
                                        )?;
                                    }
                                    s
                                },
                            },
                        ))
                    })
                    .collect::<Result<BTreeMap<_, _>, Error>>()?;
                let i = Interface {
                    methods,
                    ann: implementation
                        .attr
                        .clone()
                        .into_iter()
                        .chain([
                            Attr {
                                name: format!("generic_params"),
                                value: render_arity(arity),
                            },
                            Attr {
                                name: format!("sdk.root_path"),
                                value: format!("{path}"),
                            },
                        ])
                        .collect(),
                };
                store.store(&i)?;
                // info.interfaces.entry(i.rid()).or_default().merge(snap);
                *info.interfaces.entry(i.rid()).or_default() =
                    take(info.interfaces.entry(i.rid()).or_default()).merge(snap);
                format!("R{};{}", i.rid_str(), splat_arity(arity))
            }
        })
    }
}
