use crate::raw::{
    Allocator, Global, RawDrain, RawExtractIf, RawIntoIter, RawIter, RawIterHash, RawTable
};
use crate::{DefaultHashBuilder, Equivalent, TryReserveError};
use core::fmt::{self, Debug};
use core::hash::{BuildHasher, Hash};
use core::iter::FusedIterator;
use core::marker::PhantomData;

/// A hash multi-map implemented with quadratic probing and SIMD lookup.
///
/// The default hashing algorithm is currently [`foldhash`], though this is
/// subject to change at any point in the future. This hash function is very
/// fast for all types of keys, but this algorithm will typically *not* protect
/// against attacks such as HashDoS.
///
/// The hashing algorithm can be replaced on a per-`HashMultiMap` basis using the
/// [`default`], [`with_hasher`], and [`with_capacity_and_hasher`] methods. Many
/// alternative algorithms are available on crates.io, such as the [`fnv`] crate.
///
/// It is required that the keys implement the [`Eq`] and [`Hash`] traits, although
/// this can frequently be achieved by using `#[derive(PartialEq, Eq, Hash)]`.
/// If you implement these yourself, it is important that the following
/// property holds:
///
/// ```text
/// k1 == k2 -> hash(k1) == hash(k2)
/// ```
///
/// In other words, if two keys are equal, their hashes must be equal.
///
/// It is a logic error for a key to be modified in such a way that the key's
/// hash, as determined by the [`Hash`] trait, or its equality, as determined by
/// the [`Eq`] trait, changes while it is in the map. This is normally only
/// possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
///
/// It is also a logic error for the [`Hash`] implementation of a key to panic.
/// This is generally only possible if the trait is implemented manually. If a
/// panic does occur then the contents of the `HashMultiMap` may become corrupted and
/// some items may be dropped from the table.
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// // Type inference lets us omit an explicit type signature (which
/// // would be `HashMultiMap<String, String>` in this example).
/// let mut book_reviews = HashMultiMap::new();
///
/// // Review some books.
/// book_reviews.insert(
///     "Adventures of Huckleberry Finn".to_string(),
///     "My favorite book.".to_string(),
/// );
/// book_reviews.insert(
///     "Grimms' Fairy Tales".to_string(),
///     "Masterpiece.".to_string(),
/// );
/// book_reviews.insert(
///     "Pride and Prejudice".to_string(),
///     "Very enjoyable.".to_string(),
/// );
/// book_reviews.insert(
///     "The Adventures of Sherlock Holmes".to_string(),
///     "Eye lyked it alot.".to_string(),
/// );
///
/// // Check for a specific one.
/// // When collections store owned values (String), they can still be
/// // queried using references (&str).
/// if !book_reviews.contains_key("Les Misérables") {
///     println!("We've got {} reviews, but Les Misérables ain't one.",
///              book_reviews.len());
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// book_reviews.remove_one("The Adventures of Sherlock Holmes");
///
/// // Look up the values associated with some keys.
/// let to_find = ["Pride and Prejudice", "Alice's Adventure in Wonderland"];
/// for &book in &to_find {
///     for review in book_reviews.iter_key(book) {
///         println!("{}: {}", book, review);
///     }
/// }
///
/// // Iterate over everything.
/// for (book, review) in &book_reviews {
///     println!("{}: \"{}\"", book, review);
/// }
/// ```
///
/// The easiest way to use `HashMultiMap` with a custom key type is to derive [`Eq`] and [`Hash`].
/// We must also derive [`PartialEq`].
///
/// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
/// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
/// [`PartialEq`]: https://doc.rust-lang.org/std/cmp/trait.PartialEq.html
/// [`RefCell`]: https://doc.rust-lang.org/std/cell/struct.RefCell.html
/// [`Cell`]: https://doc.rust-lang.org/std/cell/struct.Cell.html
/// [`default`]: #method.default
/// [`with_hasher`]: #method.with_hasher
/// [`with_capacity_and_hasher`]: #method.with_capacity_and_hasher
/// [`fnv`]: https://crates.io/crates/fnv
/// [`foldhash`]: https://crates.io/crates/foldhash
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// #[derive(Hash, Eq, PartialEq, Debug)]
/// struct Viking {
///     name: String,
///     country: String,
/// }
///
/// impl Viking {
///     /// Creates a new Viking.
///     fn new(name: &str, country: &str) -> Viking {
///         Viking { name: name.to_string(), country: country.to_string() }
///     }
/// }
///
/// // Use a HashMultiMap to store the vikings' health points.
/// let mut vikings = HashMultiMap::new();
///
/// vikings.insert(Viking::new("Einar", "Norway"), 25);
/// vikings.insert(Viking::new("Olaf", "Denmark"), 24);
/// vikings.insert(Viking::new("Harald", "Iceland"), 12);
///
/// // Use derived implementation to print the status of the vikings.
/// for (viking, health) in &vikings {
///     println!("{:?} has {} hp", viking, health);
/// }
/// ```
///
/// A `HashMultiMap` with fixed list of elements can be initialized from an array:
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let timber_resources: HashMultiMap<&str, i32> = [("Norway", 100), ("Denmark", 50), ("Iceland", 10)]
///     .into_iter().collect();
/// // use the values stored in map
/// ```
pub struct HashMultiMap<K, V, S = DefaultHashBuilder, A: Allocator = Global> {
    pub(crate) hash_builder: S,
    pub(crate) table: RawTable<(K, V), A>,
}

impl<K: Clone, V: Clone, S: Clone, A: Allocator + Clone> Clone for HashMultiMap<K, V, S, A> {
    fn clone(&self) -> Self {
        HashMultiMap {
            hash_builder: self.hash_builder.clone(),
            table: self.table.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.table.clone_from(&source.table);

        // Update hash_builder only if we successfully cloned all elements.
        self.hash_builder.clone_from(&source.hash_builder);
    }
}

/// Ensures that a single closure type across uses of this which, in turn prevents multiple
/// instances of any functions like `RawTable::reserve` from being generated
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_hasher<Q, V, S>(hash_builder: &S) -> impl Fn(&(Q, V)) -> u64 + '_
where
    Q: Hash,
    S: BuildHasher,
{
    move |val| make_hash::<Q, S>(hash_builder, &val.0)
}

/// Ensures that a single closure type across uses of this which, in turn prevents multiple
/// instances of any functions like `RawTable::reserve` from being generated
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn equivalent_key<Q, K, V>(k: &Q) -> impl Fn(&(K, V)) -> bool + '_
where
    Q: Equivalent<K> + ?Sized,
{
    move |x| k.equivalent(&x.0)
}

/// Ensures that a single closure type across uses of this which, in turn prevents multiple
/// instances of any functions like `RawTable::reserve` from being generated
#[cfg_attr(feature = "inline-more", inline)]
#[allow(dead_code)]
pub(crate) fn equivalent<Q, K>(k: &Q) -> impl Fn(&K) -> bool + '_
where
    Q: Equivalent<K> + ?Sized,
{
    move |x| k.equivalent(x)
}

#[cfg(not(feature = "nightly"))]
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_hash<Q, S>(hash_builder: &S, val: &Q) -> u64
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

#[cfg(feature = "nightly")]
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_hash<Q, S>(hash_builder: &S, val: &Q) -> u64
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    hash_builder.hash_one(val)
}

#[cfg(feature = "default-hasher")]
impl<K, V> HashMultiMap<K, V, DefaultHashBuilder> {
    /// Creates an empty `HashMultiMap`.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # HashDoS resistance
    ///
    /// The `hash_builder` normally use a fixed key by default and that does
    /// not allow the `HashMultiMap` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`HashMultiMap`], for example with
    /// [`with_hasher`](HashMultiMap::with_hasher) method.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// let mut map: HashMultiMap<&str, i32> = HashMultiMap::new();
    /// assert_eq!(map.len(), 0);
    /// assert_eq!(map.capacity(), 0);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty `HashMultiMap` with the specified capacity.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// # HashDoS resistance
    ///
    /// The `hash_builder` normally use a fixed key by default and that does
    /// not allow the `HashMultiMap` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`HashMultiMap`], for example with
    /// [`with_capacity_and_hasher`](HashMultiMap::with_capacity_and_hasher) method.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// let mut map: HashMultiMap<&str, i32> = HashMultiMap::with_capacity(10);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 10);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

#[cfg(feature = "default-hasher")]
impl<K, V, A: Allocator> HashMultiMap<K, V, DefaultHashBuilder, A> {
    /// Creates an empty `HashMultiMap` using the given allocator.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # HashDoS resistance
    ///
    /// The `hash_builder` normally use a fixed key by default and that does
    /// not allow the `HashMultiMap` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`HashMultiMap`], for example with
    /// [`with_hasher_in`](HashMultiMap::with_hasher_in) method.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// use bumpalo::Bump;
    ///
    /// let bump = Bump::new();
    /// let mut map = HashMultiMap::new_in(&bump);
    ///
    /// // The created HashMultiMap holds none elements
    /// assert_eq!(map.len(), 0);
    ///
    /// // The created HashMultiMap also doesn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// // Now we insert element inside created HashMultiMap
    /// map.insert("One", 1);
    /// // We can see that the HashMultiMap holds 1 element
    /// assert_eq!(map.len(), 1);
    /// // And it also allocates some capacity
    /// assert!(map.capacity() > 1);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn new_in(alloc: A) -> Self {
        Self::with_hasher_in(DefaultHashBuilder::default(), alloc)
    }

    /// Creates an empty `HashMultiMap` with the specified capacity using the given allocator.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// # HashDoS resistance
    ///
    /// The `hash_builder` normally use a fixed key by default and that does
    /// not allow the `HashMultiMap` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`HashMultiMap`], for example with
    /// [`with_capacity_and_hasher_in`](HashMultiMap::with_capacity_and_hasher_in) method.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// use bumpalo::Bump;
    ///
    /// let bump = Bump::new();
    /// let mut map = HashMultiMap::with_capacity_in(5, &bump);
    ///
    /// // The created HashMultiMap holds none elements
    /// assert_eq!(map.len(), 0);
    /// // But it can hold at least 5 elements without reallocating
    /// let empty_map_capacity = map.capacity();
    /// assert!(empty_map_capacity >= 5);
    ///
    /// // Now we insert some 5 elements inside created HashMultiMap
    /// map.insert("One",   1);
    /// map.insert("Two",   2);
    /// map.insert("Three", 3);
    /// map.insert("Four",  4);
    /// map.insert("Five",  5);
    ///
    /// // We can see that the HashMultiMap holds 5 elements
    /// assert_eq!(map.len(), 5);
    /// // But its capacity isn't changed
    /// assert_eq!(map.capacity(), empty_map_capacity)
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self::with_capacity_and_hasher_in(capacity, DefaultHashBuilder::default(), alloc)
    }
}

impl<K, V, S> HashMultiMap<K, V, S> {
    /// Creates an empty `HashMultiMap` which will use the given hash builder to hash
    /// keys.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not
    /// allocate until it is first inserted into.
    ///
    /// # HashDoS resistance
    ///
    /// The `hash_builder` normally use a fixed key by default and that does
    /// not allow the `HashMultiMap` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`HashMultiMap`].
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the `HashMultiMap` to be useful, see its documentation for details.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    /// [`BuildHasher`]: https://doc.rust-lang.org/std/hash/trait.BuildHasher.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// use hashbrown::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = HashMultiMap::with_hasher(s);
    /// assert_eq!(map.len(), 0);
    /// assert_eq!(map.capacity(), 0);
    ///
    /// map.insert(1, 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[cfg_attr(feature = "rustc-dep-of-std", rustc_const_stable_indirect)]
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            table: RawTable::new(),
        }
    }

    /// Creates an empty `HashMultiMap` with the specified capacity, using `hash_builder`
    /// to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// # HashDoS resistance
    ///
    /// The `hash_builder` normally use a fixed key by default and that does
    /// not allow the `HashMultiMap` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`HashMultiMap`].
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the `HashMultiMap` to be useful, see its documentation for details.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    /// [`BuildHasher`]: https://doc.rust-lang.org/std/hash/trait.BuildHasher.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// use hashbrown::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = HashMultiMap::with_capacity_and_hasher(10, s);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 10);
    ///
    /// map.insert(1, 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            hash_builder,
            table: RawTable::with_capacity(capacity),
        }
    }
}

impl<K, V, S, A: Allocator> HashMultiMap<K, V, S, A> {
    /// Returns a reference to the underlying allocator.
    #[inline]
    pub fn allocator(&self) -> &A {
        self.table.allocator()
    }

    /// Creates an empty `HashMultiMap` which will use the given hash builder to hash
    /// keys. It will be allocated with the given allocator.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # HashDoS resistance
    ///
    /// The `hash_builder` normally use a fixed key by default and that does
    /// not allow the `HashMultiMap` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`HashMultiMap`].
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// use hashbrown::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = HashMultiMap::with_hasher(s);
    /// map.insert(1, 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[cfg_attr(feature = "rustc-dep-of-std", rustc_const_stable_indirect)]
    pub const fn with_hasher_in(hash_builder: S, alloc: A) -> Self {
        Self {
            hash_builder,
            table: RawTable::new_in(alloc),
        }
    }

    /// Creates an empty `HashMultiMap` with the specified capacity, using `hash_builder`
    /// to hash the keys. It will be allocated with the given allocator.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// # HashDoS resistance
    ///
    /// The `hash_builder` normally use a fixed key by default and that does
    /// not allow the `HashMultiMap` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`HashMultiMap`].
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// use hashbrown::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = HashMultiMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity_and_hasher_in(capacity: usize, hash_builder: S, alloc: A) -> Self {
        Self {
            hash_builder,
            table: RawTable::with_capacity_in(capacity, alloc),
        }
    }

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// [`BuildHasher`]: https://doc.rust-lang.org/std/hash/trait.BuildHasher.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// use hashbrown::DefaultHashBuilder;
    ///
    /// let hasher = DefaultHashBuilder::default();
    /// let map: HashMultiMap<i32, i32> = HashMultiMap::with_hasher(hasher);
    /// let hasher: &DefaultHashBuilder = map.hasher();
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the `HashMultiMap<K, V>` might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// let map: HashMultiMap<i32, i32> = HashMultiMap::with_capacity(100);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 100);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn capacity(&self) -> usize {
        self.table.capacity()
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// assert_eq!(map.len(), 3);
    /// let mut vec: Vec<&str> = Vec::new();
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    ///     vec.push(*key);
    /// }
    ///
    /// // The `Keys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// assert_eq!(map.len(), 3);
    /// let mut vec: Vec<i32> = Vec::new();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    ///     vec.push(*val);
    /// }
    ///
    /// // The `Values` iterator produces values in arbitrary order, so the
    /// // values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    ///
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for val in map.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// let mut vec: Vec<i32> = Vec::new();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    ///     vec.push(*val);
    /// }
    ///
    /// // The `Values` iterator produces values in arbitrary order, so the
    /// // values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [11, 12, 13]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// assert_eq!(map.len(), 3);
    /// let mut vec: Vec<(&str, i32)> = Vec::new();
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    ///     vec.push((*key, *val));
    /// }
    ///
    /// // The `Iter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter(&self) -> Iter<'_, K, V> {
        // Here we tie the lifetime of self to the iter.
        unsafe {
            Iter {
                inner: self.table.iter(),
                marker: PhantomData,
            }
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// let mut vec: Vec<(&str, i32)> = Vec::new();
    ///
    /// for (key, val) in &map {
    ///     println!("key: {} val: {}", key, val);
    ///     vec.push((*key, *val));
    /// }
    ///
    /// // The `Iter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [("a", 2), ("b", 4), ("c", 6)]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        // Here we tie the lifetime of self to the iter.
        unsafe {
            IterMut {
                inner: self.table.iter(),
                marker: PhantomData,
            }
        }
    }

    #[cfg(test)]
    #[cfg_attr(feature = "inline-more", inline)]
    fn raw_capacity(&self) -> usize {
        self.table.buckets()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut a = HashMultiMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn len(&self) -> usize {
        self.table.len()
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut a = HashMultiMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the
    /// allocated memory for reuse.
    ///
    /// If the returned iterator is dropped before being fully consumed, it
    /// drops the remaining key-value pairs. The returned iterator keeps a
    /// mutable borrow on the vector to optimize its implementation.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut a = HashMultiMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    /// let capacity_before_drain = a.capacity();
    ///
    /// for (k, v) in a.drain().take(1) {
    ///     assert!(k == 1 || k == 2);
    ///     assert!(v == "a" || v == "b");
    /// }
    ///
    /// // As we can see, the map is empty and contains no element.
    /// assert!(a.is_empty() && a.len() == 0);
    /// // But map capacity is equal to old one.
    /// assert_eq!(a.capacity(), capacity_before_drain);
    ///
    /// let mut a = HashMultiMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    ///
    /// {   // Iterator is dropped without being consumed.
    ///     let d = a.drain();
    /// }
    ///
    /// // But the map is empty even if we do not use Drain iterator.
    /// assert!(a.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn drain(&mut self) -> Drain<'_, K, V, A> {
        Drain {
            inner: self.table.drain(),
        }
    }

    /// Retains only the elements specified by the predicate. Keeps the
    /// allocated memory for reuse.
    ///
    /// In other words, remove all pairs `(k, v)` such that `f(&k, &mut v)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map: HashMultiMap<i32, i32> = (0..8).map(|x|(x, x*10)).collect();
    /// assert_eq!(map.len(), 8);
    ///
    /// map.retain(|&k, _| k % 2 == 0);
    ///
    /// // We can see, that the number of elements inside map is changed.
    /// assert_eq!(map.len(), 4);
    ///
    /// let mut vec: Vec<(i32, i32)> = map.iter().map(|(&k, &v)| (k, v)).collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(0, 0), (2, 20), (4, 40), (6, 60)]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        // Here we only use `iter` as a temporary, preventing use-after-free
        unsafe {
            for item in self.table.iter() {
                let &mut (ref key, ref mut value) = item.as_mut();
                if !f(key, value) {
                    self.table.erase(item);
                }
            }
        }
    }

    /// Drains elements which are true under the given predicate,
    /// and returns an iterator over the removed items.
    ///
    /// In other words, move all pairs `(k, v)` such that `f(&k, &mut v)` returns `true` out
    /// into another iterator.
    ///
    /// Note that `extract_if` lets you mutate every value in the filter closure, regardless of
    /// whether you choose to keep or remove it.
    ///
    /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped without iterating
    /// or the iteration short-circuits, then the remaining elements will be retained.
    /// Use [`retain()`] with a negated predicate if you do not need the returned iterator.
    ///
    /// Keeps the allocated memory for reuse.
    ///
    /// [`retain()`]: HashMultiMap::retain
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map: HashMultiMap<i32, i32> = (0..8).map(|x| (x, x)).collect();
    ///
    /// let drained: HashMultiMap<i32, i32> = map.extract_if(|k, _v| k % 2 == 0).collect();
    ///
    /// let mut evens = drained.keys().cloned().collect::<Vec<_>>();
    /// let mut odds = map.keys().cloned().collect::<Vec<_>>();
    /// evens.sort();
    /// odds.sort();
    ///
    /// assert_eq!(evens, vec![0, 2, 4, 6]);
    /// assert_eq!(odds, vec![1, 3, 5, 7]);
    ///
    /// let mut map: HashMultiMap<i32, i32> = (0..8).map(|x| (x, x)).collect();
    ///
    /// {   // Iterator is dropped without being consumed.
    ///     let d = map.extract_if(|k, _v| k % 2 != 0);
    /// }
    ///
    /// // ExtractIf was not exhausted, therefore no elements were drained.
    /// assert_eq!(map.len(), 8);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn extract_if<F>(&mut self, f: F) -> ExtractIf<'_, K, V, F, A>
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        ExtractIf {
            f,
            inner: RawExtractIf {
                iter: unsafe { self.table.iter() },
                table: &mut self.table,
            },
        }
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut a = HashMultiMap::new();
    /// a.insert(1, "a");
    /// let capacity_before_clear = a.capacity();
    ///
    /// a.clear();
    ///
    /// // Map is empty.
    /// assert!(a.is_empty());
    /// // But map capacity is equal to old one.
    /// assert_eq!(a.capacity(), capacity_before_clear);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear(&mut self) {
        self.table.clear();
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// let mut vec: Vec<&str> = map.into_keys().collect();
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    #[inline]
    pub fn into_keys(self) -> IntoKeys<K, V, A> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// let mut vec: Vec<i32> = map.into_values().collect();
    ///
    /// // The `IntoValues` iterator produces values in arbitrary order, so
    /// // the values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[inline]
    pub fn into_values(self) -> IntoValues<K, V, A> {
        IntoValues {
            inner: self.into_iter(),
        }
    }
}

impl<K, V, S, A> HashMultiMap<K, V, S, A>
where
    K: Eq + Hash,
    S: BuildHasher,
    A: Allocator,
{
    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `HashMultiMap`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds [`isize::MAX`] bytes and [`abort`] the program
    /// in case of allocation error. Use [`try_reserve`](HashMultiMap::try_reserve) instead
    /// if you want to handle memory allocation failure.
    ///
    /// [`isize::MAX`]: https://doc.rust-lang.org/std/primitive.isize.html
    /// [`abort`]: https://doc.rust-lang.org/alloc/alloc/fn.handle_alloc_error.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// let mut map: HashMultiMap<&str, i32> = HashMultiMap::new();
    /// // Map is empty and doesn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// map.reserve(10);
    ///
    /// // And now map can hold at least 10 elements
    /// assert!(map.capacity() >= 10);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn reserve(&mut self, additional: usize) {
        self.table
            .reserve(additional, make_hasher::<_, V, S>(&self.hash_builder));
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given `HashMultiMap<K,V>`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map: HashMultiMap<&str, isize> = HashMultiMap::new();
    /// // Map is empty and doesn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// map.try_reserve(10).expect("why is the test harness OOMing on 10 bytes?");
    ///
    /// // And now map can hold at least 10 elements
    /// assert!(map.capacity() >= 10);
    /// ```
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned:
    /// ```
    /// # fn test() {
    /// use hashbrown::HashMultiMap;
    /// use hashbrown::TryReserveError;
    /// let mut map: HashMultiMap<i32, i32> = HashMultiMap::new();
    ///
    /// match map.try_reserve(usize::MAX) {
    ///     Err(error) => match error {
    ///         TryReserveError::CapacityOverflow => {}
    ///         _ => panic!("TryReserveError::AllocError ?"),
    ///     },
    ///     _ => panic!(),
    /// }
    /// # }
    /// # fn main() {
    /// #     #[cfg(not(miri))]
    /// #     test()
    /// # }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.table
            .try_reserve(additional, make_hasher::<_, V, S>(&self.hash_builder))
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map: HashMultiMap<i32, i32> = HashMultiMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn shrink_to_fit(&mut self) {
        self.table
            .shrink_to(0, make_hasher::<_, V, S>(&self.hash_builder));
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// This function does nothing if the current capacity is smaller than the
    /// supplied minimum capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map: HashMultiMap<i32, i32> = HashMultiMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.table
            .shrink_to(min_capacity, make_hasher::<_, V, S>(&self.hash_builder));
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.iter_key(&1).next(), Some(&"a"));
    /// assert_eq!(map.iter_key(&2).next(), None);
    /// ```
    #[inline]
    pub fn iter_key<'a, 'b, Q>(&'a self, k: &'b Q) -> KeyIter<'a, 'b, Q, K, V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = make_hash::<Q, S>(&self.hash_builder, k);

        // SAFETY: KeyIter borrows lifetime from self to guarantee that
        // iterator does not outlive the raw table.
        let iter = unsafe { self.table.iter_hash(hash) };

        KeyIter {
            k,
            iter,
            marker: PhantomData,
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.iter_key_mut(&1).next() {
    ///     *x = "b";
    /// }
    /// assert_eq!(map.iter_key_mut(&1).next(), Some(&mut "b"));
    ///
    /// assert_eq!(map.iter_key_mut(&2).next(), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter_key_mut<'a, 'b, Q>(&'a mut self, k: &'b Q) -> KeyMutIter<'a, 'b, Q, K, V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = make_hash::<Q, S>(&self.hash_builder, k);

        // SAFETY: KeyMutIter borrows lifetime from self to guarantee that
        // iterator does not outlive the raw table.
        let iter = unsafe { self.table.iter_hash(hash) };

        KeyMutIter {
            k,
            iter,
            marker: PhantomData,
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.iter_key_entries(&1).next(), Some((&1, &"a")));
    /// assert_eq!(map.iter_key_entries(&2).next(), None);
    /// ```
    #[inline]
    pub fn iter_key_entries<'a, 'b, Q>(&'a self, k: &'b Q) -> EntryIter<'a, 'b, Q, K, V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = make_hash::<Q, S>(&self.hash_builder, k);

        // SAFETY: EntryIter borrows lifetime from self to guarantee that
        // iterator does not outlive the raw table.
        let iter = unsafe { self.table.iter_hash(hash) };

        EntryIter {
            k,
            iter,
            marker: PhantomData,
        }
    }

    /// Returns the key-value pair corresponding to the supplied key, with a mutable reference to value.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, "a");
    /// let (k, v) = map.iter_key_entries_mut(&1).next().unwrap();
    /// assert_eq!(k, &1);
    /// assert_eq!(v, &mut "a");
    /// *v = "b";
    /// assert_eq!(map.iter_key_entries_mut(&1).next(), Some((&1, &mut "b")));
    /// assert_eq!(map.iter_key_entries_mut(&2).next(), None);
    /// ```
    #[inline]
    pub fn iter_key_entries_mut<'a, 'b, Q>(&'a mut self, k: &'b Q) -> EntryMutIter<'a, 'b, Q, K, V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = make_hash::<Q, S>(&self.hash_builder, k);

        // SAFETY: EntryMutIter borrows lifetime from self to guarantee that
        // iterator does not outlive the raw table.
        let iter = unsafe { self.table.iter_hash(hash) };

        EntryMutIter {
            k,
            iter,
            marker: PhantomData,
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_key<Q>(&self, k: &Q) -> bool
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        if self.table.is_empty() {
            false
        } else {
            let hash = make_hash::<Q, S>(&self.hash_builder, k);
            self.table.get(hash, equivalent_key(k)).is_some()
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn count_key<Q>(&self, k: &Q) -> usize
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        if self.table.is_empty() {
            0
        } else {
            let hash = make_hash::<Q, S>(&self.hash_builder, k);
            let equivalence = equivalent_key(k);

            // SAFETY: Iterator does not outlive the scope.
            unsafe {
                self.table.iter_hash(hash).filter(|b| equivalence(b.as_ref())).count()
            }
        }
    }

    /// Inserts a key-value pair into the map.
    /// 
    /// Because the multi-map may contain multiple values for the same key, this function
    /// always adds a new entry.
    /// 
    /// Returns an inserted entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(37, "a");
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// map.insert(37, "c");
    /// assert_eq!(map.iter_key(&37).collect::<Vec<_>>(), [&"a", &"b", &"c"]);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, k: K, v: V) -> (&mut K, &mut V) {
        let hash = make_hash::<K, S>(&self.hash_builder, &k);
        let hasher = make_hasher(&self.hash_builder);
        let bucket = self.table.insert(hash, (k, v), hasher);

        // SAFETY: Returned lifetime borrows mutable reference from self.
        unsafe {
            let (k, v) = bucket.as_mut();
            (k, v)
        }
    }

    /// Removes all values with the given key from the map, returning number of values removed.
    /// Keeps the allocated memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// // The map is empty
    /// assert!(map.is_empty() && map.capacity() == 0);
    ///
    /// map.insert(1, "a");
    ///
    /// assert_eq!(map.remove_all(&1), 1);
    /// assert_eq!(map.remove_all(&1), 0);
    ///
    /// // Now map holds none elements
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_all<Q>(&mut self, k: &Q) -> usize
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = make_hash::<Q, S>(&self.hash_builder, k);
        let equivalence = equivalent_key(k);

        // SAFETY: Iterator does not outlive the scope.
        let iter = unsafe { self.table.iter_hash(hash) };
    
        let mut count = 0;
        for bucket in iter {
            unsafe {
                if equivalence(bucket.as_ref()) {
                    self.table.remove(bucket);
                    count += 1;
                }
            }
        }

        count
    }

    /// Removes one value with the given key from the map, returning the value at the key if the key
    /// was previously in the map. Keeps the allocated memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// // The map is empty
    /// assert!(map.is_empty() && map.capacity() == 0);
    ///
    /// map.insert(1, "a");
    ///
    /// assert_eq!(map.remove_one(&1), Some("a"));
    /// assert_eq!(map.remove_one(&1), None);
    ///
    /// // Now map holds none elements
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_one<Q>(&mut self, k: &Q) -> Option<V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.remove_entry(k) {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    /// Removes one entry with the given key from the map, returning the stored key and value if the
    /// key was previously in the map. Keeps the allocated memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// // The map is empty
    /// assert!(map.is_empty() && map.capacity() == 0);
    ///
    /// map.insert(1, "a");
    ///
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove(&1), None);
    ///
    /// // Now map hold none elements
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry<Q>(&mut self, k: &Q) -> Option<(K, V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = make_hash::<Q, S>(&self.hash_builder, k);
        self.table.remove_entry(hash, equivalent_key(k))
    }

    /// Returns the total amount of memory allocated internally by the hash
    /// set, in bytes.
    ///
    /// The returned number is informational only. It is intended to be
    /// primarily used for memory profiling.
    #[inline]
    pub fn allocation_size(&self) -> usize {
        self.table.allocation_size()
    }
}

impl<K, V, S, A> PartialEq for HashMultiMap<K, V, S, A>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
    A: Allocator,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.iter_key(key).any(|v| *value == *v))
    }
}

impl<K, V, S, A> Eq for HashMultiMap<K, V, S, A>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
    A: Allocator,
{
}

impl<K, V, S, A> Debug for HashMultiMap<K, V, S, A>
where
    K: Debug,
    V: Debug,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, S, A> Default for HashMultiMap<K, V, S, A>
where
    S: Default,
    A: Default + Allocator,
{
    /// Creates an empty `HashMultiMap<K, V, S, A>`, with the `Default` value for the hasher and allocator.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// // You can specify all types of HashMultiMap, including hasher and allocator.
    /// // Created map is empty and don't allocate memory
    /// let map: HashMultiMap<u32, String> = Default::default();
    /// assert_eq!(map.capacity(), 0);
    /// let map: HashMultiMap<u32, String, RandomState> = HashMultiMap::default();
    /// assert_eq!(map.capacity(), 0);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self::with_hasher_in(Default::default(), Default::default())
    }
}

// The default hasher is used to match the std implementation signature
#[cfg(feature = "default-hasher")]
impl<K, V, A, const N: usize> From<[(K, V); N]> for HashMultiMap<K, V, DefaultHashBuilder, A>
where
    K: Eq + Hash,
    A: Default + Allocator,
{
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let map1 = HashMultiMap::from([(1, 2), (3, 4)]);
    /// let map2: HashMultiMap<_, _> = [(1, 2), (3, 4)].into();
    /// assert_eq!(map1, map2);
    /// ```
    fn from(arr: [(K, V); N]) -> Self {
        arr.into_iter().collect()
    }
}

pub struct KeyIter<'a, 'b, Q: ?Sized, K, V> {
    k: &'b Q,
    iter: RawIterHash<(K, V)>,
    marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, Q, K, V> Iterator for KeyIter<'a, '_, Q, K, V>
where
    Q: Equivalent<K> + ?Sized,
{
    type Item = &'a V;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1)
    }

    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        while let Some(bucket) = self.iter.next() {
            unsafe { 
                let (k, v) = bucket.as_ref();
                if self.k.equivalent(k) {
                    return Some(v);
                }
            }
        }
        None
    }
}

pub struct KeyMutIter<'a, 'b, Q: ?Sized, K, V> {
    k: &'b Q,
    iter: RawIterHash<(K, V)>,
    marker: PhantomData<(&'a K, &'a mut V)>,
}

impl<'a, Q, K, V> Iterator for KeyMutIter<'a, '_, Q, K, V>
where
    Q: Equivalent<K> + ?Sized,
{
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<&'a mut V> {
        while let Some(bucket) = self.iter.next() {
            unsafe { 
                let (k, v) = bucket.as_mut();
                if self.k.equivalent(k) {
                    return Some(v);
                }
            }
        }
        None
    }
}

pub struct EntryIter<'a, 'b, Q: ?Sized, K, V> {
    k: &'b Q,
    iter: RawIterHash<(K, V)>,
    marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, Q, K, V> Iterator for EntryIter<'a, '_, Q, K, V>
where
    Q: Equivalent<K> + ?Sized,
{
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        while let Some(bucket) = self.iter.next() {
            unsafe { 
                let (k, v) = bucket.as_ref();
                if self.k.equivalent(k) {
                    return Some((k, v));
                }
            }
        }
        None
    }
}

pub struct EntryMutIter<'a, 'b, Q: ?Sized, K, V> {
    k: &'b Q,
    iter: RawIterHash<(K, V)>,
    marker: PhantomData<(&'a K, &'a mut V)>,
}

impl<'a, Q, K, V> Iterator for EntryMutIter<'a, '_, Q, K, V>
where
    Q: Equivalent<K> + ?Sized,
{
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        while let Some(bucket) = self.iter.next() {
            unsafe { 
                let (k, v) = bucket.as_mut();
                if self.k.equivalent(k) {
                    return Some((k, v));
                }
            }
        }
        None
    }
}

/// An iterator over the entries of a `HashMultiMap` in arbitrary order.
/// The iterator element type is `(&'a K, &'a V)`.
///
/// This `struct` is created by the [`iter`] method on [`HashMultiMap`]. See its
/// documentation for more.
///
/// [`iter`]: struct.HashMultiMap.html#method.iter
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let map: HashMultiMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
///
/// let mut iter = map.iter();
/// let mut vec = vec![iter.next(), iter.next(), iter.next()];
///
/// // The `Iter` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((&1, &"a")), Some((&2, &"b")), Some((&3, &"c"))]);
///
/// // It is fused iterator
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
/// ```
pub struct Iter<'a, K, V> {
    inner: RawIter<(K, V)>,
    marker: PhantomData<(&'a K, &'a V)>,
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<K, V> Clone for Iter<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone(),
            marker: PhantomData,
        }
    }
}

impl<K: Debug, V: Debug> fmt::Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the entries of a `HashMultiMap` in arbitrary order.
/// The iterator element type is `(&'a K, &'a mut V)`.
///
/// This `struct` is created by the [`iter_mut`] method on [`HashMultiMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: struct.HashMultiMap.html#method.iter_mut
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let mut map: HashMultiMap<_, _> = [(1, "One".to_owned()), (2, "Two".into())].into();
///
/// let mut iter = map.iter_mut();
/// iter.next().map(|(_, v)| v.push_str(" Mississippi"));
/// iter.next().map(|(_, v)| v.push_str(" Mississippi"));
///
/// // It is fused iterator
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
///
/// assert_eq!(map.iter_key(&1).next().unwrap(), &"One Mississippi".to_owned());
/// assert_eq!(map.iter_key(&2).next().unwrap(), &"Two Mississippi".to_owned());
/// ```
pub struct IterMut<'a, K, V> {
    inner: RawIter<(K, V)>,
    // To ensure invariance with respect to V
    marker: PhantomData<(&'a K, &'a mut V)>,
}

// We override the default Send impl which has K: Sync instead of K: Send. Both
// are correct, but this one is more general since it allows keys which
// implement Send but not Sync.
unsafe impl<K: Send, V: Send> Send for IterMut<'_, K, V> {}

impl<K, V> IterMut<'_, K, V> {
    /// Returns a iterator of references over the remaining items.
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            inner: self.inner.clone(),
            marker: PhantomData,
        }
    }
}

/// An owning iterator over the entries of a `HashMultiMap` in arbitrary order.
/// The iterator element type is `(K, V)`.
///
/// This `struct` is created by the [`into_iter`] method on [`HashMultiMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
/// The map cannot be used after calling that method.
///
/// [`into_iter`]: struct.HashMultiMap.html#method.into_iter
/// [`HashMultiMap`]: struct.HashMultiMap.html
/// [`IntoIterator`]: https://doc.rust-lang.org/core/iter/trait.IntoIterator.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let map: HashMultiMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
///
/// let mut iter = map.into_iter();
/// let mut vec = vec![iter.next(), iter.next(), iter.next()];
///
/// // The `IntoIter` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((1, "a")), Some((2, "b")), Some((3, "c"))]);
///
/// // It is fused iterator
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
/// ```
pub struct IntoIter<K, V, A: Allocator = Global> {
    inner: RawIntoIter<(K, V), A>,
}

impl<K, V, A: Allocator> IntoIter<K, V, A> {
    /// Returns a iterator of references over the remaining items.
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            inner: self.inner.iter(),
            marker: PhantomData,
        }
    }
}

/// An owning iterator over the keys of a `HashMultiMap` in arbitrary order.
/// The iterator element type is `K`.
///
/// This `struct` is created by the [`into_keys`] method on [`HashMultiMap`].
/// See its documentation for more.
/// The map cannot be used after calling that method.
///
/// [`into_keys`]: struct.HashMultiMap.html#method.into_keys
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let map: HashMultiMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
///
/// let mut keys = map.into_keys();
/// let mut vec = vec![keys.next(), keys.next(), keys.next()];
///
/// // The `IntoKeys` iterator produces keys in arbitrary order, so the
/// // keys must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some(1), Some(2), Some(3)]);
///
/// // It is fused iterator
/// assert_eq!(keys.next(), None);
/// assert_eq!(keys.next(), None);
/// ```
pub struct IntoKeys<K, V, A: Allocator = Global> {
    inner: IntoIter<K, V, A>,
}

impl<K, V, A: Allocator> Default for IntoKeys<K, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}
impl<K, V, A: Allocator> Iterator for IntoKeys<K, V, A> {
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<K> {
        self.inner.next().map(|(k, _)| k)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (k, _)| f(acc, k))
    }
}

impl<K, V, A: Allocator> ExactSizeIterator for IntoKeys<K, V, A> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V, A: Allocator> FusedIterator for IntoKeys<K, V, A> {}

impl<K: Debug, V: Debug, A: Allocator> fmt::Debug for IntoKeys<K, V, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|(k, _)| k))
            .finish()
    }
}

/// An owning iterator over the values of a `HashMultiMap` in arbitrary order.
/// The iterator element type is `V`.
///
/// This `struct` is created by the [`into_values`] method on [`HashMultiMap`].
/// See its documentation for more. The map cannot be used after calling that method.
///
/// [`into_values`]: struct.HashMultiMap.html#method.into_values
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let map: HashMultiMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
///
/// let mut values = map.into_values();
/// let mut vec = vec![values.next(), values.next(), values.next()];
///
/// // The `IntoValues` iterator produces values in arbitrary order, so
/// // the values must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some("a"), Some("b"), Some("c")]);
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
/// ```
pub struct IntoValues<K, V, A: Allocator = Global> {
    inner: IntoIter<K, V, A>,
}

impl<K, V, A: Allocator> Default for IntoValues<K, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}
impl<K, V, A: Allocator> Iterator for IntoValues<K, V, A> {
    type Item = V;

    #[inline]
    fn next(&mut self) -> Option<V> {
        self.inner.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (_, v)| f(acc, v))
    }
}

impl<K, V, A: Allocator> ExactSizeIterator for IntoValues<K, V, A> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V, A: Allocator> FusedIterator for IntoValues<K, V, A> {}

impl<K, V: Debug, A: Allocator> fmt::Debug for IntoValues<K, V, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|(_, v)| v))
            .finish()
    }
}

/// An iterator over the keys of a `HashMultiMap` in arbitrary order.
/// The iterator element type is `&'a K`.
///
/// This `struct` is created by the [`keys`] method on [`HashMultiMap`]. See its
/// documentation for more.
///
/// [`keys`]: struct.HashMultiMap.html#method.keys
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let map: HashMultiMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
///
/// let mut keys = map.keys();
/// let mut vec = vec![keys.next(), keys.next(), keys.next()];
///
/// // The `Keys` iterator produces keys in arbitrary order, so the
/// // keys must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some(&1), Some(&2), Some(&3)]);
///
/// // It is fused iterator
/// assert_eq!(keys.next(), None);
/// assert_eq!(keys.next(), None);
/// ```
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<K, V> Clone for Keys<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<K: Debug, V> fmt::Debug for Keys<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the values of a `HashMultiMap` in arbitrary order.
/// The iterator element type is `&'a V`.
///
/// This `struct` is created by the [`values`] method on [`HashMultiMap`]. See its
/// documentation for more.
///
/// [`values`]: struct.HashMultiMap.html#method.values
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let map: HashMultiMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
///
/// let mut values = map.values();
/// let mut vec = vec![values.next(), values.next(), values.next()];
///
/// // The `Values` iterator produces values in arbitrary order, so the
/// // values must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some(&"a"), Some(&"b"), Some(&"c")]);
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
/// ```
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<K, V> Clone for Values<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<K, V: Debug> fmt::Debug for Values<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A draining iterator over the entries of a `HashMultiMap` in arbitrary
/// order. The iterator element type is `(K, V)`.
///
/// This `struct` is created by the [`drain`] method on [`HashMultiMap`]. See its
/// documentation for more.
///
/// [`drain`]: struct.HashMultiMap.html#method.drain
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let mut map: HashMultiMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
///
/// let mut drain_iter = map.drain();
/// let mut vec = vec![drain_iter.next(), drain_iter.next(), drain_iter.next()];
///
/// // The `Drain` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((1, "a")), Some((2, "b")), Some((3, "c"))]);
///
/// // It is fused iterator
/// assert_eq!(drain_iter.next(), None);
/// assert_eq!(drain_iter.next(), None);
/// ```
pub struct Drain<'a, K, V, A: Allocator = Global> {
    inner: RawDrain<'a, (K, V), A>,
}

impl<K, V, A: Allocator> Drain<'_, K, V, A> {
    /// Returns a iterator of references over the remaining items.
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            inner: self.inner.iter(),
            marker: PhantomData,
        }
    }
}

/// A draining iterator over entries of a `HashMultiMap` which don't satisfy the predicate
/// `f(&k, &mut v)` in arbitrary order. The iterator element type is `(K, V)`.
///
/// This `struct` is created by the [`extract_if`] method on [`HashMultiMap`]. See its
/// documentation for more.
///
/// [`extract_if`]: struct.HashMultiMap.html#method.extract_if
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let mut map: HashMultiMap<i32, &str> = [(1, "a"), (2, "b"), (3, "c")].into();
///
/// let mut extract_if = map.extract_if(|k, _v| k % 2 != 0);
/// let mut vec = vec![extract_if.next(), extract_if.next()];
///
/// // The `ExtractIf` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((1, "a")),Some((3, "c"))]);
///
/// // It is fused iterator
/// assert_eq!(extract_if.next(), None);
/// assert_eq!(extract_if.next(), None);
/// drop(extract_if);
///
/// assert_eq!(map.len(), 1);
/// ```
#[must_use = "Iterators are lazy unless consumed"]
pub struct ExtractIf<'a, K, V, F, A: Allocator = Global>
where
    F: FnMut(&K, &mut V) -> bool,
{
    f: F,
    inner: RawExtractIf<'a, (K, V), A>,
}

impl<K, V, F, A> Iterator for ExtractIf<'_, K, V, F, A>
where
    F: FnMut(&K, &mut V) -> bool,
    A: Allocator,
{
    type Item = (K, V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next(|&mut (ref k, ref mut v)| (self.f)(k, v))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.inner.iter.size_hint().1)
    }
}

impl<K, V, F> FusedIterator for ExtractIf<'_, K, V, F> where F: FnMut(&K, &mut V) -> bool {}

/// A mutable iterator over the values of a `HashMultiMap` in arbitrary order.
/// The iterator element type is `&'a mut V`.
///
/// This `struct` is created by the [`values_mut`] method on [`HashMultiMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: struct.HashMultiMap.html#method.values_mut
/// [`HashMultiMap`]: struct.HashMultiMap.html
///
/// # Examples
///
/// ```
/// use hashbrown::HashMultiMap;
///
/// let mut map: HashMultiMap<_, _> = [(1, "One".to_owned()), (2, "Two".into())].into();
///
/// let mut values = map.values_mut();
/// values.next().map(|v| v.push_str(" Mississippi"));
/// values.next().map(|v| v.push_str(" Mississippi"));
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
///
/// assert_eq!(map.iter_key(&1).next().unwrap(), &"One Mississippi".to_owned());
/// assert_eq!(map.iter_key(&2).next().unwrap(), &"Two Mississippi".to_owned());
/// ```
pub struct ValuesMut<'a, K, V> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K, V, S, A: Allocator> IntoIterator for &'a HashMultiMap<K, V, S, A> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    /// Creates an iterator over the entries of a `HashMultiMap` in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// Return the same `Iter` struct as by the [`iter`] method on [`HashMultiMap`].
    ///
    /// [`iter`]: struct.HashMultiMap.html#method.iter
    /// [`HashMultiMap`]: struct.HashMultiMap.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// let map_one: HashMultiMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    /// let mut map_two = HashMultiMap::new();
    ///
    /// for (key, value) in &map_one {
    ///     println!("Key: {}, Value: {}", key, value);
    ///     map_two.insert(*key, *value);
    /// }
    ///
    /// assert_eq!(map_one, map_two);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V, S, A: Allocator> IntoIterator for &'a mut HashMultiMap<K, V, S, A> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    /// Creates an iterator over the entries of a `HashMultiMap` in arbitrary order
    /// with mutable references to the values. The iterator element type is
    /// `(&'a K, &'a mut V)`.
    ///
    /// Return the same `IterMut` struct as by the [`iter_mut`] method on
    /// [`HashMultiMap`].
    ///
    /// [`iter_mut`]: struct.HashMultiMap.html#method.iter_mut
    /// [`HashMultiMap`]: struct.HashMultiMap.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    /// let mut map: HashMultiMap<_, _> = [("a", 1), ("b", 2), ("c", 3)].into();
    ///
    /// for (key, value) in &mut map {
    ///     println!("Key: {}, Value: {}", key, value);
    ///     *value *= 2;
    /// }
    ///
    /// let mut vec = map.iter().collect::<Vec<_>>();
    /// // The `Iter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(&"a", &2), (&"b", &4), (&"c", &6)]);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K, V, S, A: Allocator> IntoIterator for HashMultiMap<K, V, S, A> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, A>;

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMultiMap;
    ///
    /// let map: HashMultiMap<_, _> = [("a", 1), ("b", 2), ("c", 3)].into();
    ///
    /// // Not possible with .iter()
    /// let mut vec: Vec<(&str, i32)> = map.into_iter().collect();
    /// // The `IntoIter` iterator produces items in arbitrary order, so
    /// // the items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> IntoIter<K, V, A> {
        IntoIter {
            inner: self.table.into_iter(),
        }
    }
}

impl<K, V> Default for Iter<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self {
            inner: Default::default(),
            marker: PhantomData,
        }
    }
}
impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some(x) => unsafe {
                let r = x.as_ref();
                Some((&r.0, &r.1))
            },
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, x| unsafe {
            let (k, v) = x.as_ref();
            f(acc, (k, v))
        })
    }
}
impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

impl<K, V> Default for IterMut<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self {
            inner: Default::default(),
            marker: PhantomData,
        }
    }
}
impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some(x) => unsafe {
                let r = x.as_mut();
                Some((&r.0, &mut r.1))
            },
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, x| unsafe {
            let (k, v) = x.as_mut();
            f(acc, (k, v))
        })
    }
}
impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for IterMut<'_, K, V> {}

impl<K, V> fmt::Debug for IterMut<'_, K, V>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<K, V, A: Allocator> Default for IntoIter<K, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}
impl<K, V, A: Allocator> Iterator for IntoIter<K, V, A> {
    type Item = (K, V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(K, V)> {
        self.inner.next()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, f)
    }
}
impl<K, V, A: Allocator> ExactSizeIterator for IntoIter<K, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V, A: Allocator> FusedIterator for IntoIter<K, V, A> {}

impl<K: Debug, V: Debug, A: Allocator> fmt::Debug for IntoIter<K, V, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<K, V> Default for Keys<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}
impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a K> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((k, _)) => Some(k),
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (k, _)| f(acc, k))
    }
}
impl<K, V> ExactSizeIterator for Keys<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for Keys<'_, K, V> {}

impl<K, V> Default for Values<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}
impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a V> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (_, v)| f(acc, v))
    }
}
impl<K, V> ExactSizeIterator for Values<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for Values<'_, K, V> {}

impl<K, V> Default for ValuesMut<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}
impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a mut V> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (_, v)| f(acc, v))
    }
}
impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

impl<K, V: Debug> fmt::Debug for ValuesMut<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|(_, val)| val))
            .finish()
    }
}

impl<K, V, A: Allocator> Iterator for Drain<'_, K, V, A> {
    type Item = (K, V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(K, V)> {
        self.inner.next()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, f)
    }
}
impl<K, V, A: Allocator> ExactSizeIterator for Drain<'_, K, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V, A: Allocator> FusedIterator for Drain<'_, K, V, A> {}

impl<K, V, A> fmt::Debug for Drain<'_, K, V, A>
where
    K: fmt::Debug,
    V: fmt::Debug,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<K, V, S, A> FromIterator<(K, V)> for HashMultiMap<K, V, S, A>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
    A: Default + Allocator,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut map =
            Self::with_capacity_and_hasher_in(iter.size_hint().0, S::default(), A::default());
        iter.for_each(|(k, v)| {
            map.insert(k, v);
        });
        map
    }
}

/// Inserts all new key-values from the iterator and replaces values with existing
/// keys with new values returned from the iterator.
impl<K, V, S, A> Extend<(K, V)> for HashMultiMap<K, V, S, A>
where
    K: Eq + Hash,
    S: BuildHasher,
    A: Allocator,
{
    /// Inserts all new key-values from the iterator to existing `HashMultiMap<K, V, S, A>`.
    /// Replace values with existing keys with new values returned from the iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::hash_multi_map::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, 100);
    ///
    /// let some_iter = [(1, 1), (2, 2)].into_iter();
    /// map.extend(some_iter);
    /// // For existing keys with adds new values returned from the iterator.
    /// // So that the map.iter_key(&1) return iterator with &100 and &1.
    /// assert_eq!(map.iter_key(&1).collect::<Vec<_>>(), [&100, &1]);
    ///
    /// let some_vec: Vec<_> = vec![(3, 3), (4, 4)];
    /// map.extend(some_vec);
    ///
    /// let some_arr = [(5, 5), (6, 6)];
    /// map.extend(some_arr);
    /// let old_map_len = map.len();
    ///
    /// // You can also extend from another HashMultiMap
    /// let mut new_map = HashMultiMap::new();
    /// new_map.extend(map);
    /// assert_eq!(new_map.len(), old_map_len);
    ///
    /// let mut vec: Vec<_> = new_map.into_iter().collect();
    /// // The `IntoIter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(1, 1), (1, 100), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)]);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        // Keys may be already present or show multiple times in the iterator.
        // Reserve the entire hint lower bound if the map is empty.
        // Otherwise reserve half the hint (rounded up), so the map
        // will only resize twice in the worst case.
        let iter = iter.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.reserve(reserve);
        iter.for_each(move |(k, v)| {
            self.insert(k, v);
        });
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_one(&mut self, (k, v): (K, V)) {
        self.insert(k, v);
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_reserve(&mut self, additional: usize) {
        // Keys may be already present or show multiple times in the iterator.
        // Reserve the entire hint lower bound if the map is empty.
        // Otherwise reserve half the hint (rounded up), so the map
        // will only resize twice in the worst case.
        let reserve = if self.is_empty() {
            additional
        } else {
            (additional + 1) / 2
        };
        self.reserve(reserve);
    }
}

/// Inserts all new key-values from the iterator and replaces values with existing
/// keys with new values returned from the iterator.
impl<'a, K, V, S, A> Extend<(&'a K, &'a V)> for HashMultiMap<K, V, S, A>
where
    K: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
    A: Allocator,
{
    /// Inserts all new key-values from the iterator to existing `HashMultiMap<K, V, S, A>`.
    /// Replace values with existing keys with new values returned from the iterator.
    /// The keys and values must implement [`Copy`] trait.
    ///
    /// [`Copy`]: https://doc.rust-lang.org/core/marker/trait.Copy.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::hash_multi_map::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, 100);
    ///
    /// let arr = [(1, 1), (2, 2)];
    /// let some_iter = arr.iter().map(|(k, v)| (k, v));
    /// map.extend(some_iter);
    /// // For existing keys with adds new values returned from the iterator.
    /// // So that the map.iter_key(&1) return iterator with &100 and &1.
    /// assert_eq!(map.iter_key(&1).collect::<Vec<_>>(), [&100, &1]);
    ///
    /// let some_vec: Vec<_> = vec![(3, 3), (4, 4)];
    /// map.extend(some_vec.iter().map(|(k, v)| (k, v)));
    ///
    /// let some_arr = [(5, 5), (6, 6)];
    /// map.extend(some_arr.iter().map(|(k, v)| (k, v)));
    ///
    /// // You can also extend from another HashMultiMap
    /// let mut new_map = HashMultiMap::new();
    /// new_map.extend(&map);
    /// assert_eq!(new_map, map);
    ///
    /// let mut vec: Vec<_> = new_map.into_iter().collect();
    /// // The `IntoIter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(1, 1), (1, 100), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)]);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(&key, &value)| (key, value)));
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_one(&mut self, (k, v): (&'a K, &'a V)) {
        self.insert(*k, *v);
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_reserve(&mut self, additional: usize) {
        Extend::<(K, V)>::extend_reserve(self, additional);
    }
}

/// Inserts all new key-values from the iterator and replaces values with existing
/// keys with new values returned from the iterator.
impl<'a, K, V, S, A> Extend<&'a (K, V)> for HashMultiMap<K, V, S, A>
where
    K: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
    A: Allocator,
{
    /// Inserts all new key-values from the iterator to existing `HashMultiMap<K, V, S, A>`.
    /// Replace values with existing keys with new values returned from the iterator.
    /// The keys and values must implement [`Copy`] trait.
    ///
    /// [`Copy`]: https://doc.rust-lang.org/core/marker/trait.Copy.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::hash_multi_map::HashMultiMap;
    ///
    /// let mut map = HashMultiMap::new();
    /// map.insert(1, 100);
    ///
    /// let arr = [(1, 1), (2, 2)];
    /// let some_iter = arr.iter();
    /// map.extend(some_iter);
    /// // For existing keys with adds new values returned from the iterator.
    /// // So that the map.iter_key(&1) return iterator with &100 and &1.
    /// assert_eq!(map.iter_key(&1).collect::<Vec<_>>(), [&100, &1]);
    ///
    /// let some_vec: Vec<_> = vec![(3, 3), (4, 4)];
    /// map.extend(&some_vec);
    ///
    /// let some_arr = [(5, 5), (6, 6)];
    /// map.extend(&some_arr);
    ///
    /// let mut vec: Vec<_> = map.into_iter().collect();
    /// // The `IntoIter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(1, 1), (1, 100), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)]);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = &'a (K, V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|&(key, value)| (key, value)));
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_one(&mut self, &(k, v): &'a (K, V)) {
        self.insert(k, v);
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_reserve(&mut self, additional: usize) {
        Extend::<(K, V)>::extend_reserve(self, additional);
    }
}

#[allow(dead_code)]
fn assert_covariance() {
    fn map_key<'new>(v: HashMultiMap<&'static str, u8>) -> HashMultiMap<&'new str, u8> {
        v
    }
    fn map_val<'new>(v: HashMultiMap<u8, &'static str>) -> HashMultiMap<u8, &'new str> {
        v
    }
    fn iter_key<'a, 'new>(v: Iter<'a, &'static str, u8>) -> Iter<'a, &'new str, u8> {
        v
    }
    fn iter_val<'a, 'new>(v: Iter<'a, u8, &'static str>) -> Iter<'a, u8, &'new str> {
        v
    }
    fn into_iter_key<'new, A: Allocator>(
        v: IntoIter<&'static str, u8, A>,
    ) -> IntoIter<&'new str, u8, A> {
        v
    }
    fn into_iter_val<'new, A: Allocator>(
        v: IntoIter<u8, &'static str, A>,
    ) -> IntoIter<u8, &'new str, A> {
        v
    }
    fn keys_key<'a, 'new>(v: Keys<'a, &'static str, u8>) -> Keys<'a, &'new str, u8> {
        v
    }
    fn keys_val<'a, 'new>(v: Keys<'a, u8, &'static str>) -> Keys<'a, u8, &'new str> {
        v
    }
    fn values_key<'a, 'new>(v: Values<'a, &'static str, u8>) -> Values<'a, &'new str, u8> {
        v
    }
    fn values_val<'a, 'new>(v: Values<'a, u8, &'static str>) -> Values<'a, u8, &'new str> {
        v
    }
    fn drain<'new>(
        d: Drain<'static, &'static str, &'static str>,
    ) -> Drain<'new, &'new str, &'new str> {
        d
    }
}

#[cfg(test)]
mod test_map {
    use super::DefaultHashBuilder;
    use super::HashMultiMap;
    use alloc::string::{String, ToString};
    use alloc::sync::Arc;
    use allocator_api2::alloc::{AllocError, Allocator, Global};
    use core::alloc::Layout;
    use core::ptr::NonNull;
    use core::sync::atomic::{AtomicI8, Ordering};
    use std::borrow::ToOwned;
    use std::cell::RefCell;
    use std::vec::Vec;

    macro_rules! assert_iter_eq {
        ($left:expr, $right:expr $(,)?) => {
            match (&mut $left.into_iter(), &mut $right.into_iter()) {
                (left_val, right_val) => {
                    for (idx, (left, right)) in left_val.by_ref().zip(&mut *right_val).enumerate() {
                        assert_eq!(left, right, "Elements at '{idx}' are not equal");
                    }

                    assert_eq!(left_val.next(), None, "left has more elements");
                    assert_eq!(right_val.next(), None, "left has more elements");
                }
            }
        };
    }

    #[test]
    fn test_zero_capacities() {
        type HM = HashMultiMap<i32, i32>;

        let m = HM::new();
        assert_eq!(m.capacity(), 0);

        let m = HM::default();
        assert_eq!(m.capacity(), 0);

        let m = HM::with_hasher(DefaultHashBuilder::default());
        assert_eq!(m.capacity(), 0);

        let m = HM::with_capacity(0);
        assert_eq!(m.capacity(), 0);

        let m = HM::with_capacity_and_hasher(0, DefaultHashBuilder::default());
        assert_eq!(m.capacity(), 0);

        let mut m = HM::new();
        m.insert(1, 1);
        m.insert(2, 2);
        m.remove_all(&1);
        m.remove_all(&2);
        m.shrink_to_fit();
        assert_eq!(m.capacity(), 0);

        let mut m = HM::new();
        m.reserve(0);
        assert_eq!(m.capacity(), 0);
    }

    #[test]
    fn test_create_capacity_zero() {
        let mut m = HashMultiMap::with_capacity(0);

        m.insert(1, 1);

        assert!(m.contains_key(&1));
        assert!(!m.contains_key(&0));
    }

    #[test]
    fn test_insert() {
        let mut m = HashMultiMap::new();
        assert_eq!(m.len(), 0);
        m.insert(1, 2);
        assert_eq!(m.len(), 1);
        m.insert(2, 4);
        assert_eq!(m.len(), 2);
        assert_iter_eq!(m.iter_key(&1), [&2]);
        assert_iter_eq!(m.iter_key(&2), [&4]);
    }

    #[test]
    fn test_clone() {
        let mut m = HashMultiMap::new();
        assert_eq!(m.len(), 0);
        m.insert(1, 2);
        assert_eq!(m.len(), 1);
        m.insert(2, 4);
        assert_eq!(m.len(), 2);
        #[allow(clippy::redundant_clone)]
        let m2 = m.clone();
        assert_iter_eq!(m2.iter_key(&1), [&2]);
        assert_iter_eq!(m2.iter_key(&2), [&4]);
        assert_eq!(m2.len(), 2);
    }

    #[test]
    fn test_clone_from() {
        let mut m = HashMultiMap::new();
        let mut m2 = HashMultiMap::new();
        assert_eq!(m.len(), 0);
        m.insert(1, 2);
        assert_eq!(m.len(), 1);
        m.insert(2, 4);
        assert_eq!(m.len(), 2);
        m2.clone_from(&m);
        assert_iter_eq!(m2.iter_key(&1), [&2]);
        assert_iter_eq!(m2.iter_key(&2), [&4]);
        assert_eq!(m2.len(), 2);
    }

    thread_local! { static DROP_VECTOR: RefCell<Vec<i32>> = const { RefCell::new(Vec::new()) } }

    #[derive(Hash, PartialEq, Eq)]
    struct Droppable {
        k: usize,
    }

    impl Droppable {
        fn new(k: usize) -> Droppable {
            DROP_VECTOR.with(|slot| {
                slot.borrow_mut()[k] += 1;
            });

            Droppable { k }
        }
    }

    impl Drop for Droppable {
        fn drop(&mut self) {
            DROP_VECTOR.with(|slot| {
                slot.borrow_mut()[self.k] -= 1;
            });
        }
    }

    impl Clone for Droppable {
        fn clone(&self) -> Self {
            Droppable::new(self.k)
        }
    }

    #[test]
    fn test_drops() {
        DROP_VECTOR.with(|slot| {
            *slot.borrow_mut() = vec![0; 200];
        });

        {
            let mut m = HashMultiMap::new();

            DROP_VECTOR.with(|v| {
                for i in 0..200 {
                    assert_eq!(v.borrow()[i], 0);
                }
            });

            for i in 0..100 {
                let d1 = Droppable::new(i);
                let d2 = Droppable::new(i + 100);
                m.insert(d1, d2);
            }

            DROP_VECTOR.with(|v| {
                for i in 0..200 {
                    assert_eq!(v.borrow()[i], 1);
                }
            });

            for i in 0..50 {
                let k = Droppable::new(i);
                let v = m.remove_one(&k);

                assert!(v.is_some());

                DROP_VECTOR.with(|v| {
                    assert_eq!(v.borrow()[i], 1);
                    assert_eq!(v.borrow()[i + 100], 1);
                });
            }

            DROP_VECTOR.with(|v| {
                for i in 0..50 {
                    assert_eq!(v.borrow()[i], 0);
                    assert_eq!(v.borrow()[i + 100], 0);
                }

                for i in 50..100 {
                    assert_eq!(v.borrow()[i], 1);
                    assert_eq!(v.borrow()[i + 100], 1);
                }
            });
        }

        DROP_VECTOR.with(|v| {
            for i in 0..200 {
                assert_eq!(v.borrow()[i], 0);
            }
        });
    }

    #[test]
    fn test_into_iter_drops() {
        DROP_VECTOR.with(|v| {
            *v.borrow_mut() = vec![0; 200];
        });

        let hm = {
            let mut hm = HashMultiMap::new();

            DROP_VECTOR.with(|v| {
                for i in 0..200 {
                    assert_eq!(v.borrow()[i], 0);
                }
            });

            for i in 0..100 {
                let d1 = Droppable::new(i);
                let d2 = Droppable::new(i + 100);
                hm.insert(d1, d2);
            }

            DROP_VECTOR.with(|v| {
                for i in 0..200 {
                    assert_eq!(v.borrow()[i], 1);
                }
            });

            hm
        };

        // By the way, ensure that cloning doesn't screw up the dropping.
        drop(hm.clone());

        {
            let mut half = hm.into_iter().take(50);

            DROP_VECTOR.with(|v| {
                for i in 0..200 {
                    assert_eq!(v.borrow()[i], 1);
                }
            });

            for _ in half.by_ref() {}

            DROP_VECTOR.with(|v| {
                let nk = (0..100).filter(|&i| v.borrow()[i] == 1).count();

                let nv = (0..100).filter(|&i| v.borrow()[i + 100] == 1).count();

                assert_eq!(nk, 50);
                assert_eq!(nv, 50);
            });
        };

        DROP_VECTOR.with(|v| {
            for i in 0..200 {
                assert_eq!(v.borrow()[i], 0);
            }
        });
    }

    #[test]
    fn test_empty_remove() {
        let mut m: HashMultiMap<i32, bool> = HashMultiMap::new();
        assert_eq!(m.remove_one(&0), None);
    }

    #[test]
    fn test_empty_iter() {
        let mut m: HashMultiMap<i32, bool> = HashMultiMap::new();
        assert_eq!(m.drain().next(), None);
        assert_eq!(m.keys().next(), None);
        assert_eq!(m.values().next(), None);
        assert_eq!(m.values_mut().next(), None);
        assert_eq!(m.iter().next(), None);
        assert_eq!(m.iter_mut().next(), None);
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());
        assert_eq!(m.into_iter().next(), None);
    }

    #[test]
    #[cfg_attr(miri, ignore)] // FIXME: takes too long
    fn test_lots_of_insertions() {
        let mut m = HashMultiMap::new();

        // Try this a few times to make sure we never screw up the hashmap's
        // internal state.
        for _ in 0..10 {
            assert!(m.is_empty());

            for i in 1..1001 {
                m.insert(i, i);

                for j in 1..=i {
                    let r = m.iter_key(&j);
                    assert_iter_eq!(r, Some(&j));
                }

                for j in i + 1..1001 {
                    let r = m.iter_key(&j);
                    assert_iter_eq!(r, None::<&i32>);
                }
            }

            for i in 1001..2001 {
                assert!(!m.contains_key(&i));
            }

            // remove forwards
            for i in 1..1001 {
                assert!(m.remove_one(&i).is_some());

                for j in 1..=i {
                    assert!(!m.contains_key(&j));
                }

                for j in i + 1..1001 {
                    assert!(m.contains_key(&j));
                }
            }

            for i in 1..1001 {
                assert!(!m.contains_key(&i));
            }

            for i in 1..1001 {
                m.insert(i, i);
            }

            // remove backwards
            for i in (1..1001).rev() {
                assert!(m.remove_one(&i).is_some());

                for j in i..1001 {
                    assert!(!m.contains_key(&j));
                }

                for j in 1..i {
                    assert!(m.contains_key(&j));
                }
            }
        }
    }

    #[test]
    fn test_find_mut() {
        let mut m = HashMultiMap::new();
        m.insert(1, 12);
        m.insert(2, 8);
        m.insert(5, 14);
        let new = 100;
        match m.iter_key_mut(&5).next() {
            None => panic!(),
            Some(x) => *x = new,
        }
        assert_eq!(m.iter_key(&5).next(), Some(&new));
    }

    #[test]
    fn test_insert_multi() {
        let mut m = HashMultiMap::new();
        m.insert(1, 2);
        assert_iter_eq!(m.iter_key(&1), [&2]);
        m.insert(1, 3);
        assert_iter_eq!(m.iter_key(&1), [&2, &3]);
    }

    #[test]
    fn test_insert_conflicts() {
        let mut m = HashMultiMap::with_capacity(4);
        m.insert(1, 2);
        m.insert(5, 3);
        m.insert(9, 4);
        assert_iter_eq!(m.iter_key(&9), [&4]);
        assert_iter_eq!(m.iter_key(&5), [&3]);
        assert_iter_eq!(m.iter_key(&1), [&2]);
    }

    #[test]
    fn test_conflict_remove() {
        let mut m = HashMultiMap::with_capacity(4);
        m.insert(1, 2);
        assert_iter_eq!(m.iter_key(&1), [&2]);
        m.insert(5, 3);
        assert_iter_eq!(m.iter_key(&1), [&2]);
        assert_iter_eq!(m.iter_key(&5), [&3]);
        m.insert(9, 4);
        assert_iter_eq!(m.iter_key(&1), [&2]);
        assert_iter_eq!(m.iter_key(&5), [&3]);
        assert_iter_eq!(m.iter_key(&9), [&4]);
        assert!(m.remove_one(&1).is_some());
        assert_iter_eq!(m.iter_key(&9), [&4]);
        assert_iter_eq!(m.iter_key(&5), [&3]);
    }

    #[test]
    fn test_is_empty() {
        let mut m = HashMultiMap::with_capacity(4);
        m.insert(1, 2);
        assert!(!m.is_empty());
        assert!(m.remove_one(&1).is_some());
        assert!(m.is_empty());
    }

    #[test]
    fn test_remove() {
        let mut m = HashMultiMap::new();
        m.insert(1, 2);
        assert_eq!(m.remove_one(&1), Some(2));
        assert_eq!(m.remove_one(&1), None);
    }

    #[test]
    fn test_remove_entry() {
        let mut m = HashMultiMap::new();
        m.insert(1, 2);
        assert_eq!(m.remove_entry(&1), Some((1, 2)));
        assert_eq!(m.remove_one(&1), None);
    }

    #[test]
    fn test_iterate() {
        let mut m = HashMultiMap::with_capacity(4);
        for i in 0..32 {
            m.insert(i, i * 2);
        }
        assert_eq!(m.len(), 32);

        let mut observed: u32 = 0;

        for (k, v) in &m {
            assert_eq!(*v, *k * 2);
            observed |= 1 << *k;
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

    #[test]
    fn test_keys() {
        let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
        let map: HashMultiMap<_, _> = vec.into_iter().collect();
        let keys: Vec<_> = map.keys().copied().collect();
        assert_eq!(keys.len(), 3);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
        assert!(keys.contains(&3));
    }

    #[test]
    fn test_values() {
        let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
        let map: HashMultiMap<_, _> = vec.into_iter().collect();
        let values: Vec<_> = map.values().copied().collect();
        assert_eq!(values.len(), 3);
        assert!(values.contains(&'a'));
        assert!(values.contains(&'b'));
        assert!(values.contains(&'c'));
    }

    #[test]
    fn test_values_mut() {
        let vec = vec![(1, 1), (2, 2), (3, 3)];
        let mut map: HashMultiMap<_, _> = vec.into_iter().collect();
        for value in map.values_mut() {
            *value *= 2;
        }
        let values: Vec<_> = map.values().copied().collect();
        assert_eq!(values.len(), 3);
        assert!(values.contains(&2));
        assert!(values.contains(&4));
        assert!(values.contains(&6));
    }

    #[test]
    fn test_into_keys() {
        let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
        let map: HashMultiMap<_, _> = vec.into_iter().collect();
        let keys: Vec<_> = map.into_keys().collect();

        assert_eq!(keys.len(), 3);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
        assert!(keys.contains(&3));
    }

    #[test]
    fn test_into_values() {
        let vec = vec![(1, 'a'), (2, 'b'), (1, 'c')];
        let map: HashMultiMap<_, _> = vec.into_iter().collect();
        let values: Vec<_> = map.into_values().collect();

        assert_eq!(values.len(), 3);
        assert!(values.contains(&'a'));
        assert!(values.contains(&'b'));
        assert!(values.contains(&'c'));
    }

    #[test]
    fn test_find() {
        let mut m = HashMultiMap::new();
        assert!(m.iter_key(&1).next().is_none());
        m.insert(1, 2);
        match m.iter_key(&1).next() {
            None => panic!(),
            Some(v) => assert_eq!(*v, 2),
        }
    }

    #[test]
    fn test_eq() {
        let mut m1 = HashMultiMap::new();
        m1.insert(1, 2);
        m1.insert(2, 3);
        m1.insert(3, 4);

        let mut m2 = HashMultiMap::new();
        m2.insert(1, 2);
        m2.insert(2, 3);

        assert!(m1 != m2);

        m2.insert(3, 4);

        assert_eq!(m1, m2);
    }

    #[test]
    fn test_show() {
        let mut map = HashMultiMap::new();
        let empty: HashMultiMap<i32, i32> = HashMultiMap::new();

        map.insert(1, 2);
        map.insert(3, 4);

        let map_str = format!("{map:?}");

        assert!(map_str == "{1: 2, 3: 4}" || map_str == "{3: 4, 1: 2}");
        assert_eq!(format!("{empty:?}"), "{}");
    }

    #[test]
    fn test_expand() {
        let mut m = HashMultiMap::new();

        assert_eq!(m.len(), 0);
        assert!(m.is_empty());

        let mut i = 0;
        let old_raw_cap = m.raw_capacity();
        while old_raw_cap == m.raw_capacity() {
            m.insert(i, i);
            i += 1;
        }

        assert_eq!(m.len(), i);
        assert!(!m.is_empty());
    }

    #[test]
    fn test_behavior_resize_policy() {
        let mut m = HashMultiMap::new();

        assert_eq!(m.len(), 0);
        assert_eq!(m.raw_capacity(), 1);
        assert!(m.is_empty());

        m.insert(0, 0);
        m.remove_one(&0);
        assert!(m.is_empty());
        let initial_raw_cap = m.raw_capacity();
        m.reserve(initial_raw_cap);
        let raw_cap = m.raw_capacity();

        assert_eq!(raw_cap, initial_raw_cap * 2);

        let mut i = 0;
        for _ in 0..raw_cap * 3 / 4 {
            m.insert(i, i);
            i += 1;
        }
        // three quarters full

        assert_eq!(m.len(), i);
        assert_eq!(m.raw_capacity(), raw_cap);

        for _ in 0..raw_cap / 4 {
            m.insert(i, i);
            i += 1;
        }
        // half full

        let new_raw_cap = m.raw_capacity();
        assert_eq!(new_raw_cap, raw_cap * 2);

        for _ in 0..raw_cap / 2 - 1 {
            i -= 1;
            m.remove_one(&i);
            assert_eq!(m.raw_capacity(), new_raw_cap);
        }
        // A little more than one quarter full.
        m.shrink_to_fit();
        assert_eq!(m.raw_capacity(), raw_cap);
        // again, a little more than half full
        for _ in 0..raw_cap / 2 {
            i -= 1;
            m.remove_one(&i);
        }
        m.shrink_to_fit();

        assert_eq!(m.len(), i);
        assert!(!m.is_empty());
        assert_eq!(m.raw_capacity(), initial_raw_cap);
    }

    #[test]
    fn test_reserve_shrink_to_fit() {
        let mut m = HashMultiMap::new();
        m.insert(0, 0);
        m.remove_one(&0);
        assert!(m.capacity() >= m.len());
        for i in 0..128 {
            m.insert(i, i);
        }
        m.reserve(256);

        let usable_cap = m.capacity();
        for i in 128..(128 + 256) {
            m.insert(i, i);
            assert_eq!(m.capacity(), usable_cap);
        }

        for i in 100..(128 + 256) {
            assert_eq!(m.remove_one(&i), Some(i));
        }
        m.shrink_to_fit();

        assert_eq!(m.len(), 100);
        assert!(!m.is_empty());
        assert!(m.capacity() >= m.len());

        for i in 0..100 {
            assert_eq!(m.remove_one(&i), Some(i));
        }
        m.shrink_to_fit();
        m.insert(0, 0);

        assert_eq!(m.len(), 1);
        assert!(m.capacity() >= m.len());
        assert_eq!(m.remove_one(&0), Some(0));
    }

    #[test]
    fn test_from_iter() {
        let xs = [(1, 1), (2, 2), (2, 7), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: HashMultiMap<_, _> = xs.iter().copied().collect();

        for &(k, v) in &xs {
            assert!(map.iter_key(&k).any(|val| val == &v));
        }

        assert_eq!(map.iter().len(), xs.len());
    }

    #[test]
    fn test_size_hint() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: HashMultiMap<_, _> = xs.iter().copied().collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_iter_len() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: HashMultiMap<_, _> = xs.iter().copied().collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.len(), 3);
    }

    #[test]
    fn test_mut_size_hint() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let mut map: HashMultiMap<_, _> = xs.iter().copied().collect();

        let mut iter = map.iter_mut();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_iter_mut_len() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let mut map: HashMultiMap<_, _> = xs.iter().copied().collect();

        let mut iter = map.iter_mut();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.len(), 3);
    }

    #[test]
    #[allow(clippy::needless_borrow)]
    fn test_extend_ref_kv_tuple() {
        use std::ops::AddAssign;
        let mut a = HashMultiMap::new();
        a.insert(0, 0);

        fn create_arr<T: AddAssign<T> + Copy, const N: usize>(start: T, step: T) -> [(T, T); N] {
            let mut outs: [(T, T); N] = [(start, start); N];
            let mut element = step;
            outs.iter_mut().skip(1).for_each(|(k, v)| {
                *k += element;
                *v += element;
                element += step;
            });
            outs
        }

        let for_iter: Vec<_> = (1..100).map(|i| (i, i)).collect();
        let iter = for_iter.iter();
        let vec: Vec<_> = (100..200).map(|i| (i, i)).collect();
        a.extend(iter);
        a.extend(&vec);
        a.extend(create_arr::<i32, 100>(200, 1));

        assert_eq!(a.len(), 300);

        for item in 0..300 {
            assert_iter_eq!(a.iter_key(&item), [&item]);
        }
    }

    #[test]
    fn test_capacity_not_less_than_len() {
        let mut a = HashMultiMap::new();
        let mut item = 0;

        for _ in 0..116 {
            a.insert(item, 0);
            item += 1;
        }

        assert!(a.capacity() > a.len());

        let free = a.capacity() - a.len();
        for _ in 0..free {
            a.insert(item, 0);
            item += 1;
        }

        assert_eq!(a.len(), a.capacity());

        // Insert at capacity should cause allocation.
        a.insert(item, 0);
        assert!(a.capacity() > a.len());
    }

    #[test]
    fn test_retain() {
        let mut map: HashMultiMap<i32, i32> = (0..100).map(|x| (x, x * 10)).collect();

        map.retain(|&k, _| k % 2 == 0);
        assert_eq!(map.len(), 50);
        assert_iter_eq!(map.iter_key(&2), [&20]);
        assert_iter_eq!(map.iter_key(&4), [&40]);
        assert_iter_eq!(map.iter_key(&6), [&60]);
    }

    #[test]
    fn test_extract_if() {
        {
            let mut map: HashMultiMap<i32, i32> = (0..8).map(|x| (x, x * 10)).collect();
            let drained = map.extract_if(|&k, _| k % 2 == 0);
            let mut out = drained.collect::<Vec<_>>();
            out.sort_unstable();
            assert_eq!(vec![(0, 0), (2, 20), (4, 40), (6, 60)], out);
            assert_eq!(map.len(), 4);
        }
        {
            let mut map: HashMultiMap<i32, i32> = (0..8).map(|x| (x, x * 10)).collect();
            map.extract_if(|&k, _| k % 2 == 0).for_each(drop);
            assert_eq!(map.len(), 4);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)] // FIXME: no OOM signalling (https://github.com/rust-lang/miri/issues/613)
    fn test_try_reserve() {
        use crate::TryReserveError::{AllocError, CapacityOverflow};

        const MAX_ISIZE: usize = isize::MAX as usize;

        let mut empty_bytes: HashMultiMap<u8, u8> = HashMultiMap::new();

        if let Err(CapacityOverflow) = empty_bytes.try_reserve(usize::MAX) {
        } else {
            panic!("usize::MAX should trigger an overflow!");
        }

        if let Err(CapacityOverflow) = empty_bytes.try_reserve(MAX_ISIZE) {
        } else {
            panic!("isize::MAX should trigger an overflow!");
        }

        if let Err(AllocError { .. }) = empty_bytes.try_reserve(MAX_ISIZE / 5) {
        } else {
            // This may succeed if there is enough free memory. Attempt to
            // allocate a few more hashmaps to ensure the allocation will fail.
            let mut empty_bytes2: HashMultiMap<u8, u8> = HashMultiMap::new();
            let _ = empty_bytes2.try_reserve(MAX_ISIZE / 5);
            let mut empty_bytes3: HashMultiMap<u8, u8> = HashMultiMap::new();
            let _ = empty_bytes3.try_reserve(MAX_ISIZE / 5);
            let mut empty_bytes4: HashMultiMap<u8, u8> = HashMultiMap::new();
            if let Err(AllocError { .. }) = empty_bytes4.try_reserve(MAX_ISIZE / 5) {
            } else {
                panic!("isize::MAX / 5 should trigger an OOM!");
            }
        }
    }

    #[test]
    fn test_const_with_hasher() {
        use core::hash::BuildHasher;
        use std::collections::hash_map::DefaultHasher;

        #[derive(Clone)]
        struct MyHasher;
        impl BuildHasher for MyHasher {
            type Hasher = DefaultHasher;

            fn build_hasher(&self) -> DefaultHasher {
                DefaultHasher::new()
            }
        }

        const EMPTY_MAP: HashMultiMap<u32, std::string::String, MyHasher> =
            HashMultiMap::with_hasher(MyHasher);

        let mut map = EMPTY_MAP;
        map.insert(17, "seventeen".to_owned());
        assert_iter_eq!(["seventeen"], map.iter_key(&17));
    }

    #[test]
    #[should_panic = "panic in drop"]
    fn test_clone_from_double_drop() {
        #[derive(Clone)]
        struct CheckedDrop {
            panic_in_drop: bool,
            dropped: bool,
        }
        impl Drop for CheckedDrop {
            fn drop(&mut self) {
                if self.panic_in_drop {
                    self.dropped = true;
                    panic!("panic in drop");
                }
                if self.dropped {
                    panic!("double drop");
                }
                self.dropped = true;
            }
        }
        const DISARMED: CheckedDrop = CheckedDrop {
            panic_in_drop: false,
            dropped: false,
        };
        const ARMED: CheckedDrop = CheckedDrop {
            panic_in_drop: true,
            dropped: false,
        };

        let mut map1 = HashMultiMap::new();
        map1.insert(1, DISARMED);
        map1.insert(2, DISARMED);
        map1.insert(3, DISARMED);
        map1.insert(4, DISARMED);

        let mut map2 = HashMultiMap::new();
        map2.insert(1, DISARMED);
        map2.insert(2, ARMED);
        map2.insert(3, DISARMED);
        map2.insert(4, DISARMED);

        map2.clone_from(&map1);
    }

    #[test]
    #[should_panic = "panic in clone"]
    fn test_clone_from_memory_leaks() {
        use alloc::vec::Vec;

        struct CheckedClone {
            panic_in_clone: bool,
            need_drop: Vec<i32>,
        }
        impl Clone for CheckedClone {
            fn clone(&self) -> Self {
                if self.panic_in_clone {
                    panic!("panic in clone")
                }
                Self {
                    panic_in_clone: self.panic_in_clone,
                    need_drop: self.need_drop.clone(),
                }
            }
        }
        let mut map1 = HashMultiMap::new();
        map1.insert(
            1,
            CheckedClone {
                panic_in_clone: false,
                need_drop: vec![0, 1, 2],
            },
        );
        map1.insert(
            2,
            CheckedClone {
                panic_in_clone: false,
                need_drop: vec![3, 4, 5],
            },
        );
        map1.insert(
            3,
            CheckedClone {
                panic_in_clone: true,
                need_drop: vec![6, 7, 8],
            },
        );
        let _map2 = map1.clone();
    }

    struct MyAllocInner {
        drop_count: Arc<AtomicI8>,
    }

    #[derive(Clone)]
    struct MyAlloc {
        _inner: Arc<MyAllocInner>,
    }

    impl MyAlloc {
        fn new(drop_count: Arc<AtomicI8>) -> Self {
            MyAlloc {
                _inner: Arc::new(MyAllocInner { drop_count }),
            }
        }
    }

    impl Drop for MyAllocInner {
        fn drop(&mut self) {
            println!("MyAlloc freed.");
            self.drop_count.fetch_sub(1, Ordering::SeqCst);
        }
    }

    unsafe impl Allocator for MyAlloc {
        fn allocate(&self, layout: Layout) -> std::result::Result<NonNull<[u8]>, AllocError> {
            let g = Global;
            g.allocate(layout)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            let g = Global;
            g.deallocate(ptr, layout)
        }
    }

    #[test]
    fn test_hashmap_into_iter_bug() {
        let dropped: Arc<AtomicI8> = Arc::new(AtomicI8::new(1));

        {
            let mut map = HashMultiMap::with_capacity_in(10, MyAlloc::new(dropped.clone()));
            for i in 0..10 {
                map.insert(i, "i".to_string());
            }

            for (k, v) in map {
                println!("{}, {}", k, v);
            }
        }

        // All allocator clones should already be dropped.
        assert_eq!(dropped.load(Ordering::SeqCst), 0);
    }

    #[derive(Debug)]
    struct CheckedCloneDrop<T> {
        panic_in_clone: bool,
        panic_in_drop: bool,
        dropped: bool,
        data: T,
    }

    impl<T> CheckedCloneDrop<T> {
        fn new(panic_in_clone: bool, panic_in_drop: bool, data: T) -> Self {
            CheckedCloneDrop {
                panic_in_clone,
                panic_in_drop,
                dropped: false,
                data,
            }
        }
    }

    impl<T: Clone> Clone for CheckedCloneDrop<T> {
        fn clone(&self) -> Self {
            if self.panic_in_clone {
                panic!("panic in clone")
            }
            Self {
                panic_in_clone: self.panic_in_clone,
                panic_in_drop: self.panic_in_drop,
                dropped: self.dropped,
                data: self.data.clone(),
            }
        }
    }

    impl<T> Drop for CheckedCloneDrop<T> {
        fn drop(&mut self) {
            if self.panic_in_drop {
                self.dropped = true;
                panic!("panic in drop");
            }
            if self.dropped {
                panic!("double drop");
            }
            self.dropped = true;
        }
    }

    /// Return hashmap with predefined distribution of elements.
    /// All elements will be located in the same order as elements
    /// returned by iterator.
    ///
    /// This function does not panic, but returns an error as a `String`
    /// to distinguish between a test panic and an error in the input data.
    fn get_test_map<I, T, A>(
        iter: I,
        mut fun: impl FnMut(u64) -> T,
        alloc: A,
    ) -> Result<HashMultiMap<u64, CheckedCloneDrop<T>, DefaultHashBuilder, A>, String>
    where
        I: Iterator<Item = (bool, bool)> + Clone + ExactSizeIterator,
        A: Allocator,
        T: PartialEq + core::fmt::Debug,
    {
        use crate::scopeguard::guard;

        let mut map: HashMultiMap<u64, CheckedCloneDrop<T>, _, A> =
            HashMultiMap::with_capacity_in(iter.size_hint().0, alloc);
        {
            let mut guard = guard(&mut map, |map| {
                for (_, value) in map.iter_mut() {
                    value.panic_in_drop = false
                }
            });

            let mut count = 0;
            // Hash and Key must be equal to each other for controlling the elements placement.
            for (panic_in_clone, panic_in_drop) in iter.clone() {
                if core::mem::needs_drop::<T>() && panic_in_drop {
                    return Err(String::from(
                        "panic_in_drop can be set with a type that doesn't need to be dropped",
                    ));
                }
                guard.table.insert(
                    count,
                    (
                        count,
                        CheckedCloneDrop::new(panic_in_clone, panic_in_drop, fun(count)),
                    ),
                    |(k, _)| *k,
                );
                count += 1;
            }

            // Let's check that all elements are located as we wanted
            let mut check_count = 0;
            for ((key, value), (panic_in_clone, panic_in_drop)) in guard.iter().zip(iter) {
                if *key != check_count {
                    return Err(format!(
                        "key != check_count,\nkey: `{}`,\ncheck_count: `{}`",
                        key, check_count
                    ));
                }
                if value.dropped
                    || value.panic_in_clone != panic_in_clone
                    || value.panic_in_drop != panic_in_drop
                    || value.data != fun(check_count)
                {
                    return Err(format!(
                        "Value is not equal to expected,\nvalue: `{:?}`,\nexpected: \
                        `CheckedCloneDrop {{ panic_in_clone: {}, panic_in_drop: {}, dropped: {}, data: {:?} }}`",
                        value, panic_in_clone, panic_in_drop, false, fun(check_count)
                    ));
                }
                check_count += 1;
            }

            if guard.len() != check_count as usize {
                return Err(format!(
                    "map.len() != check_count,\nmap.len(): `{}`,\ncheck_count: `{}`",
                    guard.len(),
                    check_count
                ));
            }

            if count != check_count {
                return Err(format!(
                    "count != check_count,\ncount: `{}`,\ncheck_count: `{}`",
                    count, check_count
                ));
            }
            core::mem::forget(guard);
        }
        Ok(map)
    }

    const DISARMED: bool = false;
    const ARMED: bool = true;

    const ARMED_FLAGS: [bool; 8] = [
        DISARMED, DISARMED, DISARMED, ARMED, DISARMED, DISARMED, DISARMED, DISARMED,
    ];

    const DISARMED_FLAGS: [bool; 8] = [
        DISARMED, DISARMED, DISARMED, DISARMED, DISARMED, DISARMED, DISARMED, DISARMED,
    ];

    #[test]
    #[should_panic = "panic in clone"]
    fn test_clone_memory_leaks_and_double_drop_one() {
        let dropped: Arc<AtomicI8> = Arc::new(AtomicI8::new(2));

        {
            assert_eq!(ARMED_FLAGS.len(), DISARMED_FLAGS.len());

            let map: HashMultiMap<u64, CheckedCloneDrop<Vec<u64>>, DefaultHashBuilder, MyAlloc> =
                match get_test_map(
                    ARMED_FLAGS.into_iter().zip(DISARMED_FLAGS),
                    |n| vec![n],
                    MyAlloc::new(dropped.clone()),
                ) {
                    Ok(map) => map,
                    Err(msg) => panic!("{msg}"),
                };

            // Clone should normally clone a few elements, and then (when the
            // clone function panics), deallocate both its own memory, memory
            // of `dropped: Arc<AtomicI8>` and the memory of already cloned
            // elements (Vec<i32> memory inside CheckedCloneDrop).
            let _map2 = map.clone();
        }
    }

    #[test]
    #[should_panic = "panic in drop"]
    fn test_clone_memory_leaks_and_double_drop_two() {
        let dropped: Arc<AtomicI8> = Arc::new(AtomicI8::new(2));

        {
            assert_eq!(ARMED_FLAGS.len(), DISARMED_FLAGS.len());

            let map: HashMultiMap<u64, CheckedCloneDrop<u64>, DefaultHashBuilder, _> = match get_test_map(
                DISARMED_FLAGS.into_iter().zip(DISARMED_FLAGS),
                |n| n,
                MyAlloc::new(dropped.clone()),
            ) {
                Ok(map) => map,
                Err(msg) => panic!("{msg}"),
            };

            let mut map2 = match get_test_map(
                DISARMED_FLAGS.into_iter().zip(ARMED_FLAGS),
                |n| n,
                MyAlloc::new(dropped.clone()),
            ) {
                Ok(map) => map,
                Err(msg) => panic!("{msg}"),
            };

            // The `clone_from` should try to drop the elements of `map2` without
            // double drop and leaking the allocator. Elements that have not been
            // dropped leak their memory.
            map2.clone_from(&map);
        }
    }

    /// We check that we have a working table if the clone operation from another
    /// thread ended in a panic (when buckets of maps are equal to each other).
    #[test]
    fn test_catch_panic_clone_from_when_len_is_equal() {
        use std::thread;

        let dropped: Arc<AtomicI8> = Arc::new(AtomicI8::new(2));

        {
            assert_eq!(ARMED_FLAGS.len(), DISARMED_FLAGS.len());

            let mut map = match get_test_map(
                DISARMED_FLAGS.into_iter().zip(DISARMED_FLAGS),
                |n| vec![n],
                MyAlloc::new(dropped.clone()),
            ) {
                Ok(map) => map,
                Err(msg) => panic!("{msg}"),
            };

            thread::scope(|s| {
                let result: thread::ScopedJoinHandle<'_, String> = s.spawn(|| {
                    let scope_map =
                        match get_test_map(ARMED_FLAGS.into_iter().zip(DISARMED_FLAGS), |n| vec![n * 2], MyAlloc::new(dropped.clone())) {
                            Ok(map) => map,
                            Err(msg) => return msg,
                        };
                    if map.table.buckets() != scope_map.table.buckets() {
                        return format!(
                            "map.table.buckets() != scope_map.table.buckets(),\nleft: `{}`,\nright: `{}`",
                            map.table.buckets(), scope_map.table.buckets()
                        );
                    }
                    map.clone_from(&scope_map);
                    "We must fail the cloning!!!".to_owned()
                });
                if let Ok(msg) = result.join() {
                    panic!("{msg}")
                }
            });

            // Let's check that all iterators work fine and do not return elements
            // (especially `RawIterRange`, which does not depend on the number of
            // elements in the table, but looks directly at the control bytes)
            //
            // SAFETY: We know for sure that `RawTable` will outlive
            // the returned `RawIter / RawIterRange` iterator.
            assert_eq!(map.len(), 0);
            assert_eq!(map.iter().count(), 0);
            assert_eq!(unsafe { map.table.iter().count() }, 0);
            assert_eq!(unsafe { map.table.iter().iter.count() }, 0);

            for idx in 0..map.table.buckets() {
                let idx = idx as u64;
                assert!(
                    map.table.find(idx, |(k, _)| *k == idx).is_none(),
                    "Index: {idx}"
                );
            }
        }

        // All allocator clones should already be dropped.
        assert_eq!(dropped.load(Ordering::SeqCst), 0);
    }

    /// We check that we have a working table if the clone operation from another
    /// thread ended in a panic (when buckets of maps are not equal to each other).
    #[test]
    fn test_catch_panic_clone_from_when_len_is_not_equal() {
        use std::thread;

        let dropped: Arc<AtomicI8> = Arc::new(AtomicI8::new(2));

        {
            assert_eq!(ARMED_FLAGS.len(), DISARMED_FLAGS.len());

            let mut map = match get_test_map(
                [DISARMED].into_iter().zip([DISARMED]),
                |n| vec![n],
                MyAlloc::new(dropped.clone()),
            ) {
                Ok(map) => map,
                Err(msg) => panic!("{msg}"),
            };

            thread::scope(|s| {
                let result: thread::ScopedJoinHandle<'_, String> = s.spawn(|| {
                    let scope_map = match get_test_map(
                        ARMED_FLAGS.into_iter().zip(DISARMED_FLAGS),
                        |n| vec![n * 2],
                        MyAlloc::new(dropped.clone()),
                    ) {
                        Ok(map) => map,
                        Err(msg) => return msg,
                    };
                    if map.table.buckets() == scope_map.table.buckets() {
                        return format!(
                            "map.table.buckets() == scope_map.table.buckets(): `{}`",
                            map.table.buckets()
                        );
                    }
                    map.clone_from(&scope_map);
                    "We must fail the cloning!!!".to_owned()
                });
                if let Ok(msg) = result.join() {
                    panic!("{msg}")
                }
            });

            // Let's check that all iterators work fine and do not return elements
            // (especially `RawIterRange`, which does not depend on the number of
            // elements in the table, but looks directly at the control bytes)
            //
            // SAFETY: We know for sure that `RawTable` will outlive
            // the returned `RawIter / RawIterRange` iterator.
            assert_eq!(map.len(), 0);
            assert_eq!(map.iter().count(), 0);
            assert_eq!(unsafe { map.table.iter().count() }, 0);
            assert_eq!(unsafe { map.table.iter().iter.count() }, 0);

            for idx in 0..map.table.buckets() {
                let idx = idx as u64;
                assert!(
                    map.table.find(idx, |(k, _)| *k == idx).is_none(),
                    "Index: {idx}"
                );
            }
        }

        // All allocator clones should already be dropped.
        assert_eq!(dropped.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_allocation_info() {
        assert_eq!(HashMultiMap::<(), ()>::new().allocation_size(), 0);
        assert_eq!(HashMultiMap::<u32, u32>::new().allocation_size(), 0);
        assert!(
            HashMultiMap::<u32, u32>::with_capacity(1).allocation_size() > core::mem::size_of::<u32>()
        );
    }
}
