#![cfg(feature = "serde")]

use hashbrown::{HashMap, HashSet};
use serde_test::{assert_tokens, Token};

#[test]
fn map_serde_tokens_empty() {
    let map = HashMap::<char, u32>::new();

    assert_tokens(&map, &[Token::Map { len: Some(0) }, Token::MapEnd]);
}

#[test]
fn map_serde_tokens() {
    let mut map = HashMap::new();
    map.insert('a', 10);

    assert_tokens(
        &map,
        &[
            Token::Map { len: Some(1) },
            Token::Char('a'),
            Token::I32(10),
            Token::MapEnd,
        ],
    );
}

#[test]
fn set_serde_tokens_empty() {
    let set = HashSet::<u32>::new();

    assert_tokens(&set, &[Token::Seq { len: Some(0) }, Token::SeqEnd]);
}

#[test]
fn set_serde_tokens() {
    let mut set = HashSet::new();
    set.insert(10);

    assert_tokens(
        &set,
        &[
            Token::Seq { len: Some(1) },
            Token::I32(10),
            Token::SeqEnd,
        ],
    );
}
