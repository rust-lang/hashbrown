use crate::map::{make_hash, DefaultHashBuilder};
use crate::raw::{RawIntoIter, RawIter, RawTable};
use core::borrow::Borrow;
use core::fmt::{self, Debug};
use core::hash::{BuildHasher, Hash};
use core::iter::{FromIterator, FusedIterator};
use core::marker::PhantomData;
use core::mem;
use core::ops::Index;

#[cfg(test)]
pub const R: usize = 4;
#[cfg(not(test))]
pub const R: usize = 8;

#[derive(Clone)]
struct OldTable<T> {
    table: RawTable<T>,

    // We cache an iterator over the old table's buckets so we don't need to do a linear search
    // across buckets we know are empty each time we want to move more items.
    items: RawIter<T>,
}

/// A hash map variant that spreads resize load across inserts.
///
/// `IncrHashMap` uses the same underlying hash table implementation as [`HashMap`]. But where the
/// standard implementation performs all-at-once resizing when the map must grow to accommodate new
/// elements, this implementation instead spreads the resizing load across subsequent inserts.
///
/// To do this, it keeps both a new, resized map, and the old, pre-resize map around after a
/// resize. The new map starts out mostly empty, and read operations search in both tables. New
/// inserts go into the new map, but they also move a few items from the old map to the new one.
/// When the old map is empty, it is dropped, and all operations hit only the new map.
///
/// # Trade-offs
///
/// This map implementation offers more stable insert performance than [`HashMap`], but it does so
/// at a cost:
///
///  - Reads and removals of old or missing keys are slower for a while after a resize.
///  - Inserts are slower than their [`HashMap`] counterparts for a while after a resize.
///  - Memory is not reclaimed immediately after a resize, only after all the keys have been moved.
///  - [`IncrHashMap`] is slightly larger than [`HashMap`], to account for the bookkeeping needed
///    to manage two maps during and after a resize.
///
/// # Examples
///
/// ```
/// use hashbrown::IncrHashMap;
///
/// // Type inference lets us omit an explicit type signature (which
/// // would be `HashMap<String, String>` in this example).
/// let mut book_reviews = IncrHashMap::new();
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
/// book_reviews.remove("The Adventures of Sherlock Holmes");
///
/// // Look up the values associated with some keys.
/// let to_find = ["Pride and Prejudice", "Alice's Adventure in Wonderland"];
/// for &book in &to_find {
///     match book_reviews.get(book) {
///         Some(review) => println!("{}: {}", book, review),
///         None => println!("{} is unreviewed.", book)
///     }
/// }
///
/// // Look up the value for a key (will panic if the key is not found).
/// println!("Review for Jane: {}", book_reviews["Pride and Prejudice"]);
///
/// // Iterate over everything.
/// for (book, review) in &book_reviews {
///     println!("{}: \"{}\"", book, review);
/// }
/// ```
///
/// [`HashMap`]: struct.HashMap.html
pub struct IncrHashMap<K, V, S = DefaultHashBuilder> {
    hash_builder: S,
    table: RawTable<(K, V)>,
    leftovers: Option<OldTable<(K, V)>>,
}

impl<K: Clone, V: Clone, S: Clone> Clone for IncrHashMap<K, V, S> {
    fn clone(&self) -> Self {
        Self {
            hash_builder: self.hash_builder.clone(),
            table: self.table.clone(),
            leftovers: self.leftovers.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.table.clone_from(&source.table);
        self.leftovers.clone_from(&source.leftovers);

        // Update hash_builder only if we successfully cloned all elements.
        self.hash_builder.clone_from(&source.hash_builder);
    }
}

#[cfg(feature = "ahash")]
impl<K, V> IncrHashMap<K, V, DefaultHashBuilder> {
    /// Creates an empty `IncrHashMap`.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    /// let mut map: IncrHashMap<&str, i32> = IncrHashMap::new();
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty `IncrHashMap` with the specified capacity.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    /// let mut map: IncrHashMap<&str, i32> = IncrHashMap::with_capacity(10);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<K, V, S> IncrHashMap<K, V, S> {
    /// Creates an empty `IncrHashMap` which will use the given hash builder to hash keys.
    ///
    /// The created map has the default initial capacity.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the map to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    /// use hashbrown::hash_map::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = IncrHashMap::with_hasher(s);
    /// map.insert(1, 2);
    /// ```
    ///
    /// [`BuildHasher`]: ../../std/hash/trait.BuildHasher.html
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            table: RawTable::new(),
            leftovers: None,
        }
    }

    /// Creates an empty `IncrHashMap` with the specified capacity, using `hash_builder` to
    /// hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the map to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    /// use hashbrown::hash_map::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = IncrHashMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, 2);
    /// ```
    ///
    /// [`BuildHasher`]: ../../std/hash/trait.BuildHasher.html
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            hash_builder,
            table: RawTable::with_capacity(capacity),
            leftovers: None,
        }
    }

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// [`BuildHasher`]: https://doc.rust-lang.org/std/hash/trait.BuildHasher.html
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    /// use hashbrown::hash_map::DefaultHashBuilder;
    ///
    /// let hasher = DefaultHashBuilder::default();
    /// let map: IncrHashMap<i32, i32> = IncrHashMap::with_hasher(hasher);
    /// let hasher: &DefaultHashBuilder = map.hasher();
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the map might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    /// let map: IncrHashMap<i32, i32> = IncrHashMap::with_capacity(100);
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    ///
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for val in map.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter(&self) -> Iter<'_, K, V> {
        // Here we tie the lifetime of self to the iter.
        unsafe {
            Iter {
                table: self.table.iter(),
                leftovers: self.leftovers.as_ref().map(|lo| lo.items.clone()),
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        // Here we tie the lifetime of self to the iter.
        unsafe {
            IterMut {
                table: self.table.iter(),
                leftovers: self.leftovers.as_mut().map(|t| t.items.clone()),
                marker: PhantomData,
            }
        }
    }

    #[cfg(test)]
    #[cfg_attr(feature = "inline-more", inline)]
    fn raw_capacity(&self) -> (usize, Option<usize>) {
        (
            self.table.buckets(),
            self.leftovers.as_ref().map(|t| t.table.buckets()),
        )
    }

    #[cfg(test)]
    fn is_split(&self) -> bool {
        self.leftovers.is_some()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut a = IncrHashMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn len(&self) -> usize {
        self.table.len() + self.leftovers.as_ref().map(|t| t.table.len()).unwrap_or(0)
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut a = IncrHashMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut a = IncrHashMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear(&mut self) {
        let _ = self.leftovers.take();
        self.table.clear();
    }
}

impl<K, V, S> IncrHashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    #[inline]
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get_key_value(k).map(|(_, v)| v)
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    #[inline]
    pub fn get_key_value<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let hash = make_hash(&self.hash_builder, k);
        let find = |t: &RawTable<(K, V)>| {
            t.find(hash, |x| k.eq(x.0.borrow())).map(|item| unsafe {
                let &(ref key, ref value) = item.as_ref();
                (key, value)
            })
        };

        if let Some(e) = find(&self.table) {
            return Some(e);
        }

        if let Some(OldTable { ref table, .. }) = self.leftovers {
            find(table)
        } else {
            None
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get(k).is_some()
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let hash = make_hash(&self.hash_builder, k);
        let find = |t: &mut RawTable<(K, V)>| {
            t.find(hash, |x| k.eq(x.0.borrow()))
                .map(|item| unsafe { &mut item.as_mut().1 })
        };

        let e = find(&mut self.table);
        if e.is_some() {
            return e;
        }

        if let Some(OldTable { ref mut table, .. }) = self.leftovers {
            find(table)
        } else {
            None
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let hash = make_hash(&self.hash_builder, &k);

        unsafe {
            if let Some(item) = self.table.find(hash, |x| k.eq(&x.0)) {
                // The item is in the main table, so just replace it.
                // NOTE: we do not carry here to keep the happy path fast.
                Some(mem::replace(&mut item.as_mut().1, v))
            } else if let Some(ref mut lo) = self.leftovers {
                if let Some(item) = lo.table.find(hash, |x| k.eq(&x.0)) {
                    // The item is in leftover table, and hasn't been moved yet, so replace it.
                    let v = Some(mem::replace(&mut item.as_mut().1, v));
                    // Also carry over items too while we're at it.
                    self.carry();
                    v
                } else {
                    // The item is not present at all, so insert it into the main table.
                    let hash_builder = &self.hash_builder;
                    self.table
                        .insert(hash, (k, v), |x| make_hash(hash_builder, &x.0));
                    // Also carry some items over.
                    self.carry();
                    None
                }
            } else {
                if self.table.capacity() == self.table.len() {
                    // Even though this _may_ succeed without growing due to tombstones, handling
                    // that case is convoluted, so we just assume this would grow the map.
                    //
                    // We need to grow the table by at least a factor of (R + 1)/R to ensure that
                    // the new table won't _also_ grow while we're still moving items from the old
                    // one. We'll favor factor-of-two growing if that's sufficient though.
                    let need_cap = ((R + 1) / R) * self.table.len();
                    let next_table_cap = usize::max(need_cap, self.table.full_capacity() + 1);

                    let mut new_table = RawTable::with_capacity(next_table_cap);
                    let hash_builder = &self.hash_builder;
                    new_table.insert(hash, (k, v), |x| make_hash(hash_builder, &x.0));
                    let old_table = mem::replace(&mut self.table, new_table);
                    let old_table_items = old_table.iter();
                    self.leftovers = Some(OldTable {
                        table: old_table,
                        items: old_table_items,
                    });
                    self.carry();
                } else {
                    let hash_builder = &self.hash_builder;
                    self.table
                        .insert(hash, (k, v), |x| make_hash(hash_builder, &x.0));
                }
                None
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn carry(&mut self) {
        if let Some(ref mut lo) = self.leftovers {
            let hash_builder = &self.hash_builder;
            for _ in 0..R {
                // It is safe to continue to access this iterator because:
                //  - we have not de-allocated the table it points into
                //  - we have not grown or shrunk the table it points into
                //
                // NOTE: Calling next here could be expensive, as the iter needs to search for the
                // next non-empty bucket. as the map grows in size, that search time will increase
                // linearly.
                if let Some(e) = lo.items.next() {
                    // We need to remove the item in this bucket from the old map
                    // to the resized map, without shrinking the old map.
                    let (k, v) = unsafe {
                        lo.table.erase_no_drop(&e);
                        e.read()
                    };
                    let hash = make_hash(&self.hash_builder, &k);
                    self.table
                        .insert(hash, (k, v), |x| make_hash(hash_builder, &x.0));
                } else {
                    // The resize is finally fully complete.
                    let _ = self.leftovers.take();
                    break;
                }
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.remove_entry(k).map(|(_, v)| v)
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
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
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        unsafe {
            let hash = make_hash(&self.hash_builder, &k);
            if let Some(item) = self.table.find(hash, |x| k.eq(x.0.borrow())) {
                self.table.erase_no_drop(&item);
                Some(item.read())
            } else if let Some(ref mut lo) = self.leftovers {
                if let Some(item) = lo.table.find(hash, |x| k.eq(x.0.borrow())) {
                    lo.table.erase_no_drop(&item);

                    // By changing the state of the table, we have invalidated the table iterator
                    // we keep for what elements are left to move. So, we re-compute it.
                    //
                    // TODO: We should be able to "fix up" the iterator rather than replace it,
                    // which would save us from iterating over the prefix of empty buckets we've
                    // left in our wake from the moves so far.
                    lo.items = lo.table.iter();
                    Some(item.read())
                } else {
                    None
                }
            } else {
                None
            }
        }
    }
}

impl<K, V, S> PartialEq for IncrHashMap<K, V, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, S> Eq for IncrHashMap<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, S> Debug for IncrHashMap<K, V, S>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, S> Default for IncrHashMap<K, V, S>
where
    S: Default,
{
    /// Creates an empty `IncrHashMap<K, V, S>`, with the `Default` value for the hasher.
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<K, Q: ?Sized, V, S> Index<&Q> for IncrHashMap<K, V, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
    S: BuildHasher,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `HashMap`.
    #[cfg_attr(feature = "inline-more", inline)]
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

/// An iterator over the entries of a `IncrHashMap`.
///
/// This `struct` is created by the [`iter`] method on [`IncrHashMap`]. See its
/// documentation for more.
///
/// [`iter`]: struct.IncrHashMap.html#method.iter
/// [`IncrHashMap`]: struct.IncrHashMap.html
pub struct Iter<'a, K, V> {
    table: RawIter<(K, V)>,
    leftovers: Option<RawIter<(K, V)>>,
    marker: PhantomData<(&'a K, &'a V)>,
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<K, V> Clone for Iter<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Iter {
            table: self.table.clone(),
            leftovers: self.leftovers.clone(),
            marker: PhantomData,
        }
    }
}

impl<K: Debug, V: Debug> fmt::Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the entries of a `IncrHashMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`IncrHashMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: struct.IncrHashMap.html#method.iter_mut
/// [`IncrHashMap`]: struct.IncrHashMap.html
pub struct IterMut<'a, K, V> {
    table: RawIter<(K, V)>,
    leftovers: Option<RawIter<(K, V)>>,
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
            table: self.table.clone(),
            leftovers: self.leftovers.clone(),
            marker: PhantomData,
        }
    }
}

/// An owning iterator over the entries of a `IncrHashMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`IncrHashMap`]
/// (provided by the `IntoIterator` trait). See its documentation for more.
///
/// [`into_iter`]: struct.IncrHashMap.html#method.into_iter
/// [`IncrHashMap`]: struct.IncrHashMap.html
pub struct IntoIter<K, V> {
    table: RawIntoIter<(K, V)>,
    leftovers: Option<RawIntoIter<(K, V)>>,
}

impl<K, V> IntoIter<K, V> {
    /// Returns a iterator of references over the remaining items.
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            table: self.table.iter(),
            leftovers: self.leftovers.as_ref().map(|i| i.iter()),
            marker: PhantomData,
        }
    }
}

/// An iterator over the keys of a `IncrHashMap`.
///
/// This `struct` is created by the [`keys`] method on [`IncrHashMap`]. See its
/// documentation for more.
///
/// [`keys`]: struct.IncrHashMap.html#method.keys
/// [`IncrHashMap`]: struct.IncrHashMap.html
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

/// An iterator over the values of a `IncrHashMap`.
///
/// This `struct` is created by the [`values`] method on [`IncrHashMap`]. See its
/// documentation for more.
///
/// [`values`]: struct.IncrHashMap.html#method.values
/// [`IncrHashMap`]: struct.IncrHashMap.html
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

/// A mutable iterator over the values of a `IncrHashMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`IncrHashMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: struct.IncrHashMap.html#method.values_mut
/// [`IncrHashMap`]: struct.IncrHashMap.html
pub struct ValuesMut<'a, K, V> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K, V, S> IntoIterator for &'a IncrHashMap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V, S> IntoIterator for &'a mut IncrHashMap<K, V, S> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K, V, S> IntoIterator for IncrHashMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::IncrHashMap;
    ///
    /// let mut map = IncrHashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// // Not possible with .iter()
    /// let vec: Vec<(&str, i32)> = map.into_iter().collect();
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter {
            table: self.table.into_iter(),
            leftovers: self.leftovers.map(|t| {
                // TODO: make this re-use knowledge of progress from t.items
                t.table.into_iter()
            }),
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        let leftovers = &mut self.leftovers;
        self.table
            .next()
            .or_else(|| leftovers.as_mut()?.next())
            .map(|x| unsafe {
                let r = x.as_ref();
                (&r.0, &r.1)
            })
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (mut lo, mut hi) = self.table.size_hint();
        if let Some(ref left) = self.leftovers {
            let (lo2, hi2) = left.size_hint();
            lo += lo2;
            if let (Some(ref mut hi), Some(hi2)) = (&mut hi, hi2) {
                *hi += hi2;
            }
        }
        (lo, hi)
    }
}
impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.table.len() + self.leftovers.as_ref().map(|lo| lo.len()).unwrap_or(0)
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        let leftovers = &mut self.leftovers;
        self.table
            .next()
            .or_else(|| leftovers.as_mut()?.next())
            .map(|x| unsafe {
                let r = x.as_mut();
                (&r.0, &mut r.1)
            })
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (mut lo, mut hi) = self.table.size_hint();
        if let Some(ref left) = self.leftovers {
            let (lo2, hi2) = left.size_hint();
            lo += lo2;
            if let (Some(ref mut hi), Some(hi2)) = (&mut hi, hi2) {
                *hi += hi2;
            }
        }
        (lo, hi)
    }
}
impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.table.len() + self.leftovers.as_ref().map(|lo| lo.len()).unwrap_or(0)
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

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(K, V)> {
        let leftovers = &mut self.leftovers;
        self.table.next().or_else(|| leftovers.as_mut()?.next())
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (mut lo, mut hi) = self.table.size_hint();
        if let Some(ref left) = self.leftovers {
            let (lo2, hi2) = left.size_hint();
            lo += lo2;
            if let (Some(ref mut hi), Some(hi2)) = (&mut hi, hi2) {
                *hi += hi2;
            }
        }
        (lo, hi)
    }
}
impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.table.len() + self.leftovers.as_ref().map(|lo| lo.len()).unwrap_or(0)
    }
}
impl<K, V> FusedIterator for IntoIter<K, V> {}

impl<K: Debug, V: Debug> fmt::Debug for IntoIter<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a K> {
        self.inner.next().map(|(k, _)| k)
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<K, V> ExactSizeIterator for Keys<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for Keys<'_, K, V> {}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, v)| v)
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<K, V> ExactSizeIterator for Values<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for Values<'_, K, V> {}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a mut V> {
        self.inner.next().map(|(_, v)| v)
    }
    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

impl<K, V> fmt::Debug for ValuesMut<'_, K, V>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.iter()).finish()
    }
}

impl<K, V, S> FromIterator<(K, V)> for IncrHashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity_and_hasher(iter.size_hint().0, S::default());
        iter.for_each(|(k, v)| {
            map.insert(k, v);
        });
        map
    }
}

#[allow(dead_code)]
fn assert_covariance() {
    fn map_key<'new>(v: IncrHashMap<&'static str, u8>) -> IncrHashMap<&'new str, u8> {
        v
    }
    fn map_val<'new>(v: IncrHashMap<u8, &'static str>) -> IncrHashMap<u8, &'new str> {
        v
    }
    fn iter_key<'a, 'new>(v: Iter<'a, &'static str, u8>) -> Iter<'a, &'new str, u8> {
        v
    }
    fn iter_val<'a, 'new>(v: Iter<'a, u8, &'static str>) -> Iter<'a, u8, &'new str> {
        v
    }
    fn into_iter_key<'new>(v: IntoIter<&'static str, u8>) -> IntoIter<&'new str, u8> {
        v
    }
    fn into_iter_val<'new>(v: IntoIter<u8, &'static str>) -> IntoIter<u8, &'new str> {
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
}

#[cfg(test)]
mod test_map {
    use super::DefaultHashBuilder;
    use super::IncrHashMap;
    use std::cell::RefCell;
    use std::usize;
    use std::vec::Vec;

    #[test]
    fn test_zero_capacities() {
        type HM = IncrHashMap<i32, i32>;

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
    }

    #[test]
    fn test_create_capacity_zero() {
        let mut m = IncrHashMap::with_capacity(0);

        assert!(m.insert(1, 1).is_none());

        assert!(m.contains_key(&1));
        assert!(!m.contains_key(&0));
    }

    #[test]
    fn test_insert() {
        let mut m = IncrHashMap::new();
        assert_eq!(m.len(), 0);
        assert!(m.insert(1, 2).is_none());
        assert_eq!(m.len(), 1);
        assert!(m.insert(2, 4).is_none());
        assert_eq!(m.len(), 2);
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&2).unwrap(), 4);
    }

    #[test]
    fn test_split_insert() {
        // the code below assumes that R is 4
        assert_eq!(super::R, 4);

        let mut m = IncrHashMap::new();
        assert_eq!(m.capacity(), 0);
        // three inserts won't split
        for i in 1..=3 {
            m.insert(i, i);
            assert_eq!(m.get(&i), Some(&i));
            assert_eq!(m.capacity(), 3);
        }
        // fourth insert will split and migrate all elements
        assert!(!m.is_split());
        m.insert(4, 4);
        // capacity should now be doubled
        assert_eq!(m.capacity(), 7);
        // and there should be no leftovers
        assert!(!m.is_split());
        assert_eq!(m.table.len(), 4);
        for i in 1..=4 {
            assert_eq!(m.get(&i), Some(&i));
        }

        // move to next split point
        for i in 5..=7 {
            m.insert(i, i);
            assert_eq!(m.get(&i), Some(&i));
            assert_eq!(m.capacity(), 7);
        }

        // next insert will split, and move some, but not all (since R < old.len())
        m.insert(8, 8);
        // capacity should now be doubled
        assert_eq!(m.capacity(), 14);
        // and there should be leftovers
        assert!(m.is_split());
        assert_eq!(m.table.len(), 1 + super::R);
        for i in 1..=8 {
            assert_eq!(m.get(&i), Some(&i));
        }
        // check that the iterators do the right thing when split:
        assert_eq!(m.iter().count(), 8);
        for i in 1..=8 {
            assert!(m.iter().any(|(&e, _)| e == i));
        }
        assert_eq!(m.iter_mut().count(), 8);
        for i in 1..=8 {
            assert!(m.iter_mut().any(|(&e, _)| e == i));
        }

        // if we do another insert, it will move the rest of the items from the old map
        m.insert(9, 9);
        assert!(!m.is_split());
        assert_eq!(m.table.len(), 9);
        // it should not have changed capacity
        assert_eq!(m.capacity(), 14);
        for i in 1..=9 {
            assert_eq!(m.get(&i), Some(&i));
        }
    }

    #[test]
    fn test_clone() {
        let mut m = IncrHashMap::new();
        for i in 1..=8 {
            assert_eq!(m.len(), i - 1);
            assert!(m.insert(i, i + 1).is_none());
        }
        assert_eq!(m.len(), 8);
        let m2 = m.clone();
        for i in 1..=8 {
            assert_eq!(m2.get(&i).copied(), Some(i + 1));
        }
        assert_eq!(m2.len(), 8);
    }

    #[test]
    fn test_clone_from() {
        let mut m = IncrHashMap::new();
        let mut m2 = IncrHashMap::new();
        for i in 1..=8 {
            assert_eq!(m.len(), i - 1);
            assert!(m.insert(i, i + 1).is_none());
        }
        assert_eq!(m.len(), 8);
        m2.clone_from(&m);
        for i in 1..=8 {
            assert_eq!(m2.get(&i).copied(), Some(i + 1));
        }
        assert_eq!(m2.len(), 8);
    }

    thread_local! { static DROP_VECTOR: RefCell<Vec<i32>> = RefCell::new(Vec::new()) }

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
            let mut m = IncrHashMap::new();

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
                let v = m.remove(&k);

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
            let mut hm = IncrHashMap::new();

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
        let mut m: IncrHashMap<i32, bool> = IncrHashMap::new();
        assert_eq!(m.remove(&0), None);
    }

    #[test]
    fn test_empty_iter() {
        let mut m: IncrHashMap<i32, bool> = IncrHashMap::new();
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
    #[ignore]
    fn test_lots_of_insertions() {
        let mut m = IncrHashMap::new();

        // Try this a few times to make sure we never screw up the hashmap's
        // internal state.
        for _ in 0..10 {
            assert!(m.is_empty());

            for i in 1..1001 {
                assert!(m.insert(i, i).is_none());

                for j in 1..=i {
                    let r = m.get(&j);
                    assert_eq!(r, Some(&j));
                }

                for j in i + 1..1001 {
                    let r = m.get(&j);
                    assert_eq!(r, None);
                }
            }

            for i in 1001..2001 {
                assert!(!m.contains_key(&i));
            }

            // remove forwards
            for i in 1..1001 {
                assert!(m.remove(&i).is_some());

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
                assert!(m.insert(i, i).is_none());
            }

            // remove backwards
            for i in (1..1001).rev() {
                assert!(m.remove(&i).is_some());

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
        let mut m = IncrHashMap::new();
        // ensure that the map splits
        for i in 1..=6 {
            m.insert(1000 + i, i);
        }
        assert!(!m.is_split());
        assert!(m.insert(1, 12).is_none());
        assert!(!m.is_split());
        assert!(m.insert(2, 8).is_none());
        assert!(m.is_split());
        assert!(m.insert(5, 14).is_none());
        let new = 100;
        match m.get_mut(&5) {
            None => panic!(),
            Some(x) => *x = new,
        }
        assert_eq!(m.get(&5), Some(&new));
    }

    #[test]
    fn test_insert_overwrite() {
        let mut m = IncrHashMap::new();
        // ensure that the map splits
        for i in 1..=7 {
            m.insert(1000 + i, i);
        }
        assert!(!m.is_split());
        assert!(m.insert(1, 2).is_none());
        assert!(m.is_split());
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert!(!m.insert(1, 3).is_none());
        assert_eq!(*m.get(&1).unwrap(), 3);
    }

    #[test]
    fn test_insert_conflicts() {
        let mut m = IncrHashMap::with_capacity(4);
        // ensure that the map splits
        for i in 1..=7 {
            m.insert(1000 + i, i);
        }
        assert!(!m.is_split());
        assert!(m.insert(1, 2).is_none());
        assert!(m.is_split());
        assert!(m.insert(5, 3).is_none());
        assert!(m.insert(9, 4).is_none());
        assert_eq!(*m.get(&9).unwrap(), 4);
        assert_eq!(*m.get(&5).unwrap(), 3);
        assert_eq!(*m.get(&1).unwrap(), 2);
    }

    #[test]
    fn test_conflict_remove() {
        let mut m = IncrHashMap::with_capacity(4);
        // ensure that the map splits
        for i in 1..=5 {
            m.insert(1000 + i, i);
        }
        assert!(!m.is_split());
        assert!(m.insert(1, 2).is_none());
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert!(m.insert(5, 3).is_none());
        assert!(!m.is_split());
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&5).unwrap(), 3);
        assert!(m.insert(9, 4).is_none());
        assert!(m.is_split());
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&5).unwrap(), 3);
        assert_eq!(*m.get(&9).unwrap(), 4);
        assert!(m.remove(&1).is_some());
        assert_eq!(*m.get(&9).unwrap(), 4);
        assert_eq!(*m.get(&5).unwrap(), 3);
    }

    #[test]
    fn test_is_empty() {
        let mut m = IncrHashMap::with_capacity(4);
        assert!(m.insert(1, 2).is_none());
        assert!(!m.is_empty());
        assert!(m.remove(&1).is_some());
        assert!(m.is_empty());
    }

    #[test]
    fn test_remove() {
        let mut m = IncrHashMap::new();
        m.insert(1, 2);
        assert_eq!(m.remove(&1), Some(2));
        assert_eq!(m.remove(&1), None);
    }

    #[test]
    fn test_remove_entry() {
        let mut m = IncrHashMap::new();
        m.insert(1, 2);
        assert_eq!(m.remove_entry(&1), Some((1, 2)));
        assert_eq!(m.remove(&1), None);
    }

    #[test]
    fn test_iterate() {
        let mut m = IncrHashMap::with_capacity(4);
        for i in 0..32 {
            assert!(m.insert(i, i * 2).is_none());
        }
        assert!(m.is_split());
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
        let mut map = IncrHashMap::new();
        for (k, v) in (1..).zip('a'..).take(8) {
            map.insert(k, v);
        }
        assert!(map.is_split());
        let keys: Vec<_> = map.keys().cloned().collect();
        assert_eq!(keys.len(), 8);
        for i in 1..=8 {
            assert!(keys.contains(&i));
        }
    }

    #[test]
    fn test_values() {
        let mut map = IncrHashMap::new();
        for (k, v) in (1..).zip('a'..).take(8) {
            map.insert(k, v);
        }
        assert!(map.is_split());
        let values: Vec<_> = map.values().cloned().collect();
        assert_eq!(values.len(), 8);
        for c in 'a'..='g' {
            assert!(values.contains(&c));
        }
    }

    #[test]
    fn test_values_mut() {
        let mut map = IncrHashMap::new();
        for v in (1..).take(8) {
            map.insert(v, v);
        }
        assert!(map.is_split());
        for value in map.values_mut() {
            *value = (*value) * 2
        }
        let values: Vec<_> = map.values().cloned().collect();
        assert_eq!(values.len(), 8);
        for v in 1..=8 {
            let v = 2 * v;
            assert!(values.contains(&v));
        }
    }

    #[test]
    fn test_find() {
        let mut m = IncrHashMap::new();
        assert!(m.get(&1).is_none());
        m.insert(1, 2);
        match m.get(&1) {
            None => panic!(),
            Some(v) => assert_eq!(*v, 2),
        }
        assert!(!m.is_split());

        // now make it split
        for i in 1..=7 {
            m.insert(1000 + i, i);
        }
        assert!(m.is_split());
        match m.get(&1) {
            None => panic!(),
            Some(v) => assert_eq!(*v, 2),
        }

        // now make it un-split
        m.insert(1000 + 8, 8);
        assert!(!m.is_split());
        match m.get(&1) {
            None => panic!(),
            Some(v) => assert_eq!(*v, 2),
        }
    }

    #[test]
    fn test_eq() {
        let mut m1 = IncrHashMap::new();
        for (k, v) in (1..).zip('a'..).take(8) {
            m1.insert(k, v);
        }

        let mut m2 = IncrHashMap::new();
        for (k, v) in (1..).zip('a'..).take(7) {
            m2.insert(k, v);
        }

        assert!(m1 != m2);

        m2.insert(8, 'h');

        assert_eq!(m1, m2);
    }

    #[test]
    fn test_show() {
        let mut map = IncrHashMap::new();
        let empty: IncrHashMap<i32, i32> = IncrHashMap::new();

        map.insert(1, 2);
        map.insert(3, 4);

        let map_str = format!("{:?}", map);

        assert!(map_str == "{1: 2, 3: 4}" || map_str == "{3: 4, 1: 2}");
        assert_eq!(format!("{:?}", empty), "{}");
    }

    #[test]
    fn test_expand() {
        let mut m = IncrHashMap::new();

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
    fn test_from_iter() {
        let xs = (0..8).map(|v| (v, v));

        let map: IncrHashMap<_, _> = xs.clone().collect();

        for (k, v) in xs.clone() {
            assert_eq!(map.get(&k), Some(&v));
        }

        assert_eq!(map.iter().len(), xs.len());
    }

    #[test]
    fn test_size_hint() {
        let xs = (0..8).map(|v| (v, v));

        let map: IncrHashMap<_, _> = xs.clone().collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (8 - 3, Some(8 - 3)));
    }

    #[test]
    fn test_iter_len() {
        let xs = (0..8).map(|v| (v, v));

        let map: IncrHashMap<_, _> = xs.clone().collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.len(), 8 - 3);
    }

    #[test]
    fn test_mut_size_hint() {
        let xs = (0..8).map(|v| (v, v));

        let mut map: IncrHashMap<_, _> = xs.clone().collect();

        let mut iter = map.iter_mut();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (8 - 3, Some(8 - 3)));
    }

    #[test]
    fn test_iter_mut_len() {
        let xs = (0..8).map(|v| (v, v));

        let mut map: IncrHashMap<_, _> = xs.clone().collect();

        let mut iter = map.iter_mut();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.len(), 8 - 3);
    }

    #[test]
    fn test_index() {
        let mut map = IncrHashMap::new();

        for i in 1..=8 {
            map.insert(i, i);
        }
        assert!(map.is_split());

        assert_eq!(map[&2], 2);
    }

    #[test]
    #[should_panic]
    fn test_index_nonexistent() {
        let mut map = IncrHashMap::new();

        for i in 1..=8 {
            map.insert(i, i);
        }
        assert!(map.is_split());

        map[&9];
    }

    #[test]
    fn test_capacity_not_less_than_len() {
        let mut a = IncrHashMap::new();
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
}
