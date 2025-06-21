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
    ) -> Result<Vec<String>, Error>;
}
