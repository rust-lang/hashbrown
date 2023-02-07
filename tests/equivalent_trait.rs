use hashbrown::Equivalent;
use hashbrown::HashMap;

use std::hash::Hash;

#[derive(Debug, Hash)]
pub struct Pair<A, B>(pub A, pub B);

impl<A, B, C, D> PartialEq<(A, B)> for Pair<C, D>
where
    C: PartialEq<A>,
    D: PartialEq<B>,
{
    fn eq(&self, rhs: &(A, B)) -> bool {
        self.0 == rhs.0 && self.1 == rhs.1
    }
}

impl<A, B, X> Equivalent<X> for &Pair<A, B>
where
    Pair<A, B>: PartialEq<X>,
    A: Hash + Eq,
    B: Hash + Eq,
{
    fn equivalent(self, other: &X) -> bool {
        *self == *other
    }
}

#[test]
fn test_lookup() {
    let s = String::from;
    let mut map = HashMap::new();
    map.insert((s("a"), s("b")), 1);
    map.insert((s("a"), s("x")), 2);

    assert!(map.contains_key(&Pair("a", "b")));
    assert!(!map.contains_key(&Pair("b", "a")));
}

#[test]
fn test_string_str() {
    let s = String::from;
    let mut map = HashMap::new();
    map.insert(s("a"), 1);
    map.insert(s("b"), 2);
    map.insert(s("x"), 3);
    map.insert(s("y"), 4);

    assert!(map.contains_key("a"));
    assert!(!map.contains_key("z"));
    assert_eq!(map.remove("b"), Some(2));
}

#[derive(Copy, Clone)]
struct BytesAsStringRef<'a>(&'a [u8]);

impl<'a> std::hash::Hash for BytesAsStringRef<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // We have to hash exactly like a string, or else lookups will fail
        if let Ok(s) = std::str::from_utf8(self.0) {
            s.hash(state);
        }
        // else doesn't matter -- it can't be equivalent to a string anyway
    }
}

impl<'a> Equivalent<String> for BytesAsStringRef<'a> {
    fn equivalent(self, key: &String) -> bool {
        self.0 == key.as_bytes()
    }
}

#[test]
fn test_bytes_as_str() {
    let mut map: HashMap<String, i32> = HashMap::new();
    assert_eq!(map.get("123"), None);
    assert_eq!(map.get(BytesAsStringRef(b"123")), None);
    map.insert(String::from("123"), 123);
    assert_eq!(map.get("123"), Some(&123));
    assert_eq!(map.get(BytesAsStringRef(b"123")), Some(&123));
}
