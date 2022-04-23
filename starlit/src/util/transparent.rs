//! Helper traits for conversion of types that are transparent wrappers over a storage type.

/// A type using an underlying storage type as representation in memory.
///
/// # Safety
/// Every value of a type implementing this must also be a valid value for the storage type. The
/// converse does not have to hold.
pub unsafe trait Transparent: Sized + ConvertStorage {}

/// Conversion of [`Transparent`] types to their underlying storage.
pub trait ConvertStorage {
    /// The underlying storage type.
    type Storage: Sized;

    /// Converts this value to the underlying storage type.
    fn into_storage(self) -> Self::Storage;

    /// Converts a value of the underlying storage type to a value of the implementing type.
    ///
    /// # Safety
    /// The caller has to ensure that this maintains any extra invariants imposed by the
    /// implementing type. See the documentation of the implementing type for details.
    unsafe fn from_storage_unchecked(storage: Self::Storage) -> Self;
}

/// Conversion of [`Transparent`] types to their underlying storage.
pub trait ConvertStorageMut {
    /// The underlying storage type.
    type StorageMut: Sized;

    /// Converts this value to the underlying storage type, allowing mutable access.
    ///
    /// # Safety
    /// The caller has to ensure that any performed mutations maintain any extra invariants imposed
    /// by the implementing type. See the documentation of the implementing type for details.
    unsafe fn into_storage_mut(self) -> Self::StorageMut;

    /// Converts a value of the underlying storage type to a value of the implementing type.
    ///
    /// # Safety
    /// The caller has to ensure that this maintains any extra invariants imposed by the
    /// implementing type. See the documentation of the implementing type for details.
    unsafe fn from_storage_unchecked_mut(storage: Self::StorageMut) -> Self;
}

impl<'a, T: Transparent> ConvertStorage for &'a T {
    type Storage = &'a T::Storage;

    #[inline(always)]
    fn into_storage(self) -> Self::Storage {
        // SAFETY by documented invariant of types implementing `Transparent`
        unsafe { &*(self as *const _ as *const _) }
    }

    #[inline(always)]
    unsafe fn from_storage_unchecked(storage: Self::Storage) -> Self {
        &*(storage as *const _ as *const _)
    }
}

impl<'a, T: Transparent> ConvertStorage for &'a [T] {
    type Storage = &'a [T::Storage];

    #[inline(always)]
    fn into_storage(self) -> Self::Storage {
        // SAFETY by documented invariant of types implementing `Transparent`
        unsafe { &*(self as *const _ as *const _) }
    }

    #[inline(always)]
    unsafe fn from_storage_unchecked(storage: Self::Storage) -> Self {
        &*(storage as *const _ as *const _)
    }
}

impl<'a, T: Transparent> ConvertStorageMut for &'a mut T {
    type StorageMut = &'a mut T::Storage;

    #[inline(always)]
    unsafe fn into_storage_mut(self) -> Self::StorageMut {
        &mut *(self as *mut _ as *mut _)
    }

    #[inline(always)]
    unsafe fn from_storage_unchecked_mut(storage: Self::StorageMut) -> Self {
        &mut *(storage as *mut _ as *mut _)
    }
}

impl<'a, T: Transparent> ConvertStorageMut for &'a mut [T] {
    type StorageMut = &'a mut [T::Storage];

    #[inline(always)]
    unsafe fn into_storage_mut(self) -> Self::StorageMut {
        &mut *(self as *mut _ as *mut _)
    }

    #[inline(always)]
    unsafe fn from_storage_unchecked_mut(storage: Self::StorageMut) -> Self {
        &mut *(storage as *mut _ as *mut _)
    }
}
