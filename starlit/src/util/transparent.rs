//! Helper traits for conversion of types that are transparent wrappers over a storage type.

/// A type using an underlying storage type as representation in memory.
///
/// # Safety
/// Every value of a type implementing this must also be a valid value for the storage type. The
/// converse does not have to hold.
pub unsafe trait Transparent: Sized + AsStorage {}

/// Conversion of [`Transparent`] types to their underlying storage.
pub trait AsStorage {
    /// The underlying storage type.
    type Storage: Sized;

    /// Converts this value to the underlying storage type.
    fn as_storage(self) -> Self::Storage;

    /// Converts a value of the underlying storage type to a value of the implementing type.
    ///
    /// # Safety
    /// The caller has to ensure that this maintains any extra invariants imposed by the
    /// implementing type. See the documentation of the implementing type for details.
    unsafe fn from_storage_unchecked(storage: Self::Storage) -> Self;
}

/// Conversion of [`Transparent`] types to their underlying storage.
pub trait AsStorageMut {
    /// The underlying storage type.
    type StorageMut: Sized;

    /// Converts this value to the underlying storage type, allowing mutable access.
    ///
    /// # Safety
    /// The caller has to ensure that any performed mutations maintain any extra invariants imposed
    /// by the implementing type. See the documentation of the implementing type for details.
    unsafe fn as_storage_mut(self) -> Self::StorageMut;

    /// Converts a value of the underlying storage type to a value of the implementing type.
    ///
    /// # Safety
    /// The caller has to ensure that this maintains any extra invariants imposed by the
    /// implementing type. See the documentation of the implementing type for details.
    unsafe fn from_storage_unchecked_mut(storage: Self::StorageMut) -> Self;
}

macro_rules! unsafe_impl_transparent {
    ($T:ty, $S:ty) => {
        unsafe impl $crate::util::transparent::Transparent for $T {}

        impl $crate::util::transparent::AsStorage for $T {
            type Storage = $S;

            #[inline(always)]
            fn as_storage(self) -> Self::Storage {
                unsafe { ::std::mem::transmute(self) }
            }

            #[inline(always)]
            unsafe fn from_storage_unchecked(storage: Self::Storage) -> Self {
                ::std::mem::transmute(storage)
            }
        }

        ::static_assertions::assert_eq_size!($T, $S);
        ::static_assertions::assert_eq_align!($T, $S);
    };
}

impl<'a, T: Transparent> AsStorage for &'a T {
    type Storage = &'a T::Storage;

    #[inline(always)]
    fn as_storage(self) -> Self::Storage {
        // SAFETY by documented invariant of types implementing `Transparent`
        unsafe { &*(self as *const _ as *const _) }
    }

    #[inline(always)]
    unsafe fn from_storage_unchecked(storage: Self::Storage) -> Self {
        &*(storage as *const _ as *const _)
    }
}

impl<'a, T: Transparent> AsStorage for &'a [T] {
    type Storage = &'a [T::Storage];

    #[inline(always)]
    fn as_storage(self) -> Self::Storage {
        // SAFETY by documented invariant of types implementing `Transparent`
        unsafe { &*(self as *const _ as *const _) }
    }

    #[inline(always)]
    unsafe fn from_storage_unchecked(storage: Self::Storage) -> Self {
        &*(storage as *const _ as *const _)
    }
}

impl<'a, T: Transparent> AsStorageMut for &'a mut T {
    type StorageMut = &'a mut T::Storage;

    #[inline(always)]
    unsafe fn as_storage_mut(self) -> Self::StorageMut {
        &mut *(self as *mut _ as *mut _)
    }

    #[inline(always)]
    unsafe fn from_storage_unchecked_mut(storage: Self::StorageMut) -> Self {
        &mut *(storage as *mut _ as *mut _)
    }
}

impl<'a, T: Transparent> AsStorageMut for &'a mut [T] {
    type StorageMut = &'a mut [T::Storage];

    #[inline(always)]
    unsafe fn as_storage_mut(self) -> Self::StorageMut {
        &mut *(self as *mut _ as *mut _)
    }

    #[inline(always)]
    unsafe fn from_storage_unchecked_mut(storage: Self::StorageMut) -> Self {
        &mut *(storage as *mut _ as *mut _)
    }
}
