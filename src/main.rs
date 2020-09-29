use comptime_trie::{ArrayMatch, FastMatch, FullTrieMatch, JustMatch};

// just for benchmarking
fn get_input() -> String {
    let mut input = String::new();
    std::io::stdin().read_line(&mut input).unwrap();
    input.trim().to_string()
}

fn main() {
    #[derive(FullTrieMatch, FastMatch, ArrayMatch, JustMatch, Debug, PartialEq)]
    enum Names {
        FOO,
        BAR,
        BLUB,
        Z,
        AAB,
        CCCA,
        CCCB,
        CCCF,
        // r#if,
        // r#amatch,
        // r#aamatch
    }

    // for cargo asm
    let name = just_match_names(&get_input());
    dbg!(&name);
    let name = full_trie_match_names(&get_input());
    dbg!(&name);
    let name = unsafe { fast_match_names(&get_input()) };
    dbg!(&name);
    let name = array_match_names(&get_input());
    dbg!(&name);
}

#[test]
fn test() {
    #[derive(FullTrieMatch, FastMatch, ArrayMatch, JustMatch, Debug, PartialEq)]
    enum Names {
        FOO,
        BAR,
        BLUB,
        Z,
        AAB,
        CCCA,
        CCCB,
        CCCF,
        r#match,
        // r#if,
        // r#aamatch,
    }

    // just_match_names
    assert_eq!(Some(Names::FOO), just_match_names(&"FOO".to_string()));
    assert_eq!(Some(Names::Z), just_match_names(&"Z".to_string()));
    assert_eq!(None, just_match_names(&"X".to_string()));
    assert_eq!(
        Some(Names::r#match),
        just_match_names(&"r#match".to_string())
    ); // TODO filter r#
    assert_eq!(None, just_match_names(&"CCrF".to_string())); // works in safe mode

    // fast_match_names
    assert_eq!(Names::FOO, unsafe { fast_match_names(&"FOO".to_string()) });
    assert_eq!(Names::Z, unsafe { fast_match_names(&"Z".to_string()) });
    // assert_eq!( ???, unsafe { fast_match_names(&"X".to_string()) }); // sigkill
    assert_eq!(Names::r#match, unsafe {
        fast_match_names(&"r#match".to_string())
    }); // TODO filter r#
    assert_eq!(Names::CCCF, unsafe {
        fast_match_names(&"CCrF".to_string())
    }); // EEEEh this is why its unsafe ;)

    // full_trie_match_names
    assert_eq!(Some(Names::FOO), full_trie_match_names(&"FOO".to_string()));
    assert_eq!(Some(Names::Z), full_trie_match_names(&"Z".to_string()));
    assert_eq!(None, full_trie_match_names(&"X".to_string()));
    assert_eq!(
        Some(Names::r#match),
        full_trie_match_names(&"r#match".to_string())
    ); // TODO filter r#
    assert_eq!(None, full_trie_match_names(&"CCrF".to_string())); // works in safe mode

    // array_match_names
    assert_eq!(Some(Names::FOO), array_match_names(&"FOO".to_string()));
    assert_eq!(Some(Names::Z), array_match_names(&"Z".to_string()));
    assert_eq!(None, array_match_names(&"X".to_string()));
    assert_eq!(
        Some(Names::r#match),
        array_match_names(&"r#match".to_string())
    ); // TODO filter r#
    assert_eq!(None, full_trie_match_names(&"CCrF".to_string())); // works in safe mode
}
