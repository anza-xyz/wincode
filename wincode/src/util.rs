use core::{any::TypeId, marker::PhantomData, mem::transmute};

/// Ripped from the `unty` crate, but forced inline so the compiler can DCE the branch.
#[inline(always)]
pub(crate) fn type_equal<Src: ?Sized, Target: ?Sized>() -> bool {
    non_static_type_id::<Src>() == non_static_type_id::<Target>()
}

// Code by dtolnay in a bincode issue:
// https://github.com/bincode-org/bincode/issues/665#issue-1903241159
//
// All functions ripped from the `unty` crate, forced inline for branch DCE.
#[inline(always)]
fn non_static_type_id<T: ?Sized>() -> TypeId {
    trait NonStaticAny {
        fn get_type_id(&self) -> TypeId
        where
            Self: 'static;
    }

    impl<T: ?Sized> NonStaticAny for PhantomData<T> {
        #[inline(always)]
        fn get_type_id(&self) -> TypeId
        where
            Self: 'static,
        {
            TypeId::of::<T>()
        }
    }

    let phantom_data = PhantomData::<T>;
    NonStaticAny::get_type_id(unsafe {
        transmute::<&dyn NonStaticAny, &(dyn NonStaticAny + 'static)>(&phantom_data)
    })
}
