#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs, warnings)]

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

use alloc::boxed::Box;

#[cfg(not(loom))]
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use core::{
  hash::Hasher,
  ops::{Deref, DerefMut},
  ptr,
};

#[cfg(loom)]
use loom::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

#[cfg(loom)]
trait AtomicMut<T> {}

#[cfg(not(loom))]
trait AtomicMut<T> {
  fn with_mut<F, R>(&mut self, f: F) -> R
  where
    F: FnOnce(&mut *mut T) -> R;
}

#[cfg(not(loom))]
impl<T> AtomicMut<T> for AtomicPtr<T> {
  fn with_mut<F, R>(&mut self, f: F) -> R
  where
    F: FnOnce(&mut *mut T) -> R,
  {
    f(self.get_mut())
  }
}

struct Data<T> {
  refs: AtomicUsize,
  data: T,
}

/// A reference-counted pointer to a value of type `T`, which can be mutated.
///
/// > **Note: This struct is not thread-safe!!!**
///
/// `ArcMut<T>` provides shared ownership of a value of type `T`, allocated
/// in the heap. Invoking `clone` on `ArcMut` produces another pointer to the
/// same allocation in the heap. When the last `ArcMut` pointer to a given
/// allocation is destroyed, the value stored in that allocation (often
/// referred to as "inner value") is also dropped.
///
/// This is similar to `std::sync::Arc`, but it allows interior mutability.
///
/// In normal circumstances, you are not expected to use this type, but when you
/// are writing FFI code, you may need to use this type to share a value between
/// Rust and other languages, and again, if the code in other languages is concurrent,
/// you need to use a `Arc<Mutex<T>>` instead.
pub struct ArcMut<T> {
  ptr: AtomicPtr<()>,
  _marker: core::marker::PhantomData<T>,
}

impl<T> From<T> for ArcMut<T> {
  /// Converts a `T` into an `Arc<T>`
  ///
  /// The conversion moves the value into a
  /// newly allocated `Arc`. It is equivalent to
  /// calling `Arc::new(t)`.
  ///
  /// # Example
  /// ```rust
  /// # use arcmut::ArcMut;
  /// let x = 5;
  /// let arc = ArcMut::new(5);
  ///
  /// assert_eq!(ArcMut::from(x), arc);
  /// ```
  fn from(t: T) -> Self {
    Self::new(t)
  }
}

impl<T: Default> Default for ArcMut<T> {
  fn default() -> Self {
    Self::new(Default::default())
  }
}

impl<T> Clone for ArcMut<T> {
  fn clone(&self) -> Self {
    unsafe {
      let shared: *mut Data<T> = self.ptr.load(Ordering::Relaxed).cast();

      let old_size = (*shared).refs.fetch_add(1, Ordering::Release);
      if old_size > usize::MAX >> 1 {
        abort();
      }

      // Safety:
      // The ptr is always non-null, and the data is only deallocated when the
      // last ArcMut is dropped.
      Self {
        ptr: AtomicPtr::new(shared as *mut ()),
        _marker: core::marker::PhantomData,
      }
    }
  }
}

impl<T> Deref for ArcMut<T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    unsafe {
      let shared: *mut Data<T> = self.ptr.load(Ordering::Relaxed).cast();
      &(*shared).data
    }
  }
}

impl<T> DerefMut for ArcMut<T> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    unsafe {
      let shared: *mut Data<T> = self.ptr.load(Ordering::Relaxed).cast();
      &mut (*shared).data
    }
  }
}

impl<T> core::borrow::Borrow<T> for ArcMut<T> {
  fn borrow(&self) -> &T {
    self
  }
}

impl<T> core::borrow::BorrowMut<T> for ArcMut<T> {
  fn borrow_mut(&mut self) -> &mut T {
    self
  }
}

impl<T> AsRef<T> for ArcMut<T> {
  fn as_ref(&self) -> &T {
    self
  }
}

impl<T> AsMut<T> for ArcMut<T> {
  fn as_mut(&mut self) -> &mut T {
    self
  }
}

impl<T> core::fmt::Debug for ArcMut<T>
where
  T: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Debug::fmt(&**self, f)
  }
}

impl<T> core::fmt::Display for ArcMut<T>
where
  T: core::fmt::Display,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Display::fmt(&**self, f)
  }
}

impl<T> PartialEq for ArcMut<T>
where
  T: PartialEq,
{
  fn eq(&self, other: &Self) -> bool {
    **self == **other
  }
}

impl<T> Eq for ArcMut<T> where T: Eq {}

impl<T: core::hash::Hash> core::hash::Hash for ArcMut<T> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    (**self).hash(state)
  }
}

impl<T> PartialOrd for ArcMut<T>
where
  T: PartialOrd,
{
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    (**self).partial_cmp(&**other)
  }
}

impl<T> Ord for ArcMut<T>
where
  T: Ord,
{
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    (**self).cmp(&**other)
  }
}

impl<T> Drop for ArcMut<T> {
  fn drop(&mut self) {
    unsafe {
      self.ptr.with_mut(|shared| {
        let shared: *mut Data<T> = shared.cast();
        // `Shared` storage... follow the drop steps from Arc.
        if (*shared).refs.fetch_sub(1, Ordering::Release) != 1 {
          return;
        }

        // This fence is needed to prevent reordering of use of the data and
        // deletion of the data.  Because it is marked `Release`, the decreasing
        // of the reference count synchronizes with this `Acquire` fence. This
        // means that use of the data happens before decreasing the reference
        // count, which happens before this fence, which happens before the
        // deletion of the data.
        //
        // As explained in the [Boost documentation][1],
        //
        // > It is important to enforce any possible access to the object in one
        // > thread (through an existing reference) to *happen before* deleting
        // > the object in a different thread. This is achieved by a "release"
        // > operation after dropping a reference (any access to the object
        // > through this reference must obviously happened before), and an
        // > "acquire" operation before deleting the object.
        //
        // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
        //
        // Thread sanitizer does not support atomic fences. Use an atomic load
        // instead.
        (*shared).refs.load(Ordering::Acquire);
        // Drop the data
        let _ = Box::from_raw(shared);
      });
    }
  }
}

impl<T> ArcMut<T> {
  /// Constructs a new `ArcMut<T>`.
  ///
  /// # Examples
  ///
  /// ```
  /// use arcmut::ArcMut;
  ///
  /// let five = ArcMut::new(5);
  /// ```
  pub fn new(data: T) -> Self {
    let data = Box::new(Data {
      refs: AtomicUsize::new(1),
      data,
    });

    Self {
      ptr: AtomicPtr::new(Box::into_raw(data) as *mut ()),
      _marker: core::marker::PhantomData,
    }
  }

  /// Returns `true` if the two ArcMuts point to the same allocation in a vein similar to [`ptr::eq`]. This function ignores the metadata of dyn Trait pointers.
  ///
  /// # Examples
  ///
  /// ```
  /// use arcmut::ArcMut;
  ///
  /// let five = ArcMut::new(5);
  /// let same_five = ArcMut::clone(&five);
  /// let other_five = ArcMut::new(5);
  ///
  /// assert!(ArcMut::ptr_eq(&five, &same_five));
  /// assert!(!ArcMut::ptr_eq(&five, &other_five));
  /// ```
  pub fn ptr_eq(this: &Self, other: &Self) -> bool {
    let this = this.ptr.load(Ordering::Relaxed);
    let other = other.ptr.load(Ordering::Relaxed);
    ptr::eq(this, other)
  }

  /// Gets the number of strong (`ArcMut`) pointers to this allocation.
  ///
  /// # Safety
  ///
  /// This method by itself is safe, but using it correctly requires extra care.
  /// Another thread can change the strong count at any time,
  /// including potentially between calling this method and acting on the result.
  ///
  /// # Examples
  ///
  /// ```
  /// use arcmut::ArcMut;
  ///
  /// let five = ArcMut::new(5);
  /// let _also_five = ArcMut::clone(&five);
  ///
  /// // This assertion is deterministic because we haven't shared
  /// // the `Arc` between threads.
  /// assert_eq!(2, ArcMut::count(&five));
  /// ```
  pub fn count(this: &Self) -> usize {
    unsafe {
      let shared: *mut Data<T> = this.ptr.load(Ordering::Relaxed).cast();
      (*shared).refs.load(Ordering::Acquire)
    }
  }
}

unsafe impl<T: Sync + Send> Send for ArcMut<T> {}
unsafe impl<T: Sync + Send> Sync for ArcMut<T> {}

#[cfg(feature = "serde")]
const _: () = {
  use serde::{Deserialize, Serialize};

  impl<T> Serialize for ArcMut<T>
  where
    T: Serialize,
  {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
      S: serde::Serializer,
    {
      (**self).serialize(serializer)
    }
  }

  impl<'de, T> Deserialize<'de> for ArcMut<T>
  where
    T: Deserialize<'de>,
  {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
      D: serde::Deserializer<'de>,
    {
      T::deserialize(deserializer).map(Self::new)
    }
  }
};

#[inline(never)]
#[cold]
fn abort() -> ! {
  #[cfg(feature = "std")]
  {
    std::process::abort()
  }

  #[cfg(not(feature = "std"))]
  {
    struct Abort;
    impl Drop for Abort {
      fn drop(&mut self) {
        panic!();
      }
    }
    let _a = Abort;
    panic!("abort");
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use alloc::format;

  macro_rules! test {
    ($($tt:tt)*) => {
      #[cfg(loom)]
      {
        loom::model(|| {
          $($tt)*
        });
      }

      #[cfg(not(loom))]
      {
        $($tt)*
      }
    };
  }

  #[test]
  fn test_clone() {
    test! {
      let x = ArcMut::new(5);
      let y = x.clone();
      assert_eq!(5, *x);
      assert_eq!(5, *y);
    }
  }

  #[test]
  fn test_deref() {
    test! {
      let x = ArcMut::new(5);
      assert_eq!(5, *x);
    }
  }

  #[test]
  fn test_deref_mut() {
    test! {
      let mut x = ArcMut::new(5);
      *x = 10;
      assert_eq!(10, *x);
    }
  }

  #[test]
  fn test_as_ref() {
    test! {
      let x = ArcMut::new(5);
      assert_eq!(5, *x.as_ref());
    }
  }

  #[test]
  fn test_as_mut() {
    test! {
      let mut x = ArcMut::new(5);
      *x.as_mut() = 10;
      assert_eq!(10, *x.as_ref());
    }
  }

  #[test]
  fn test_default() {
    test! {
      let x: ArcMut<i32> = Default::default();
      assert_eq!(0, *x);
    }
  }

  #[test]
  fn test_from() {
    test! {
      let x = 5;
      let x = ArcMut::from(x);
      assert_eq!(5, *x);
    }
  }

  #[test]
  fn test_partial_eq() {
    test! {
      let x = ArcMut::new(5);
      let y = ArcMut::new(5);
      assert_eq!(x, y);
    }
  }

  #[test]
  fn test_partial_ord() {
    test! {
      let x = ArcMut::new(5);
      let y = ArcMut::new(5);
      assert_eq!(x.partial_cmp(&y), Some(core::cmp::Ordering::Equal));
    }
  }

  #[test]
  fn test_ord() {
    test! {
      let x = ArcMut::new(5);
      let y = ArcMut::new(5);
      assert_eq!(x.cmp(&y), core::cmp::Ordering::Equal)
    }
  }

  #[test]
  #[cfg(feature = "std")]
  fn test_hash() {
    test! {
      use core::hash::{Hash, Hasher};
      let x = ArcMut::new(5);
      let mut hasher = std::collections::hash_map::DefaultHasher::new();
      x.hash(&mut hasher);
      let hash = hasher.finish();
      assert_eq!(hash, 14828406784900857967u64);
    }
  }

  #[test]
  fn test_fmt_debug() {
    test! {
      let x = ArcMut::new(5);
      assert_eq!("5", format!("{:?}", x));
    }
  }

  #[test]
  fn test_fmt_display() {
    test!(
      let x = ArcMut::new(5);
      assert_eq!("5", format!("{}", x));
    );
  }

  #[test]
  fn test_ptr_eq() {
    test!(
      let x = ArcMut::new(5);
    let y = ArcMut::clone(&x);
    let z = ArcMut::new(5);
    assert!(ArcMut::ptr_eq(&x, &y));
    assert!(!ArcMut::ptr_eq(&x, &z));
    );
  }

  #[test]
  fn test_count() {
    test!(
      let x = ArcMut::new(5);
    assert_eq!(1, ArcMut::count(&x));
    let y = ArcMut::clone(&x);
    assert_eq!(2, ArcMut::count(&x));
    assert_eq!(2, ArcMut::count(&y));
    drop(x);
    assert_eq!(1, ArcMut::count(&y));
    drop(y);
    );
  }

  #[test]
  #[cfg(feature = "std")]
  fn test_thread() {
    #[cfg(loom)]
    use loom::thread;

    #[cfg(not(loom))]
    use std::thread;

    test!(
      let arc = ArcMut::new(alloc::vec![100u8; 100]);
      for _ in 0..2 {
        let data = arc.clone();
        thread::spawn(move || {
          assert_eq!(data.len(), 100,);
          assert_eq!(data.as_ref(), &[100u8; 100]);
        });
      }
      while ArcMut::count(&arc) > 1 {
        thread::yield_now();
      }

      assert_eq!(arc.len(), 100,);

      assert_eq!(arc.as_ref(), &[100u8; 100]);
    );
  }
}
