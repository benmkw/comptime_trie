#![feature(iter_partition_in_place)]

//! # A crate to experiment with different ways of converting strings into enums
//! This could be extended to convert any compile time known set of types
//! which can be converted to an array into a set of corresponding variants/ an enum.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::DeriveInput;

/// Derive match expression with converts a String to an Enum
/// # Example
/// ```
/// #[derive(comptime_trie::JustMatch, Debug, PartialEq)]
/// enum Names {
///     FOO,
///     BAR,
///     BLUB,
///     Z,
///     AAB,
///     CCCA,
///     CCCB,
///     CCCF,
/// }
///
/// assert_eq!(Some(Names::FOO), just_match_names("FOO"));
/// ```
///
/// # Generated Code
///
/// ```
/// # enum Names {
/// #     FOO,
/// #     BAR,
/// #     BLUB,
/// #     Z,
/// #     AAB,
/// #     CCCA,
/// #     CCCB,
/// #     CCCF,
/// # }
///
/// fn just_match_names(s: &str) -> Option<Names> {
///     match s {
///         "FOO" => Some(Names::FOO),
///         "BAR" => Some(Names::BAR),
///         "BLUB" => Some(Names::BLUB),
///         "Z" => Some(Names::Z),
///         "AAB" => Some(Names::AAB),
///         "CCCA" => Some(Names::CCCA),
///         "CCCB" => Some(Names::CCCB),
///         "CCCF" => Some(Names::CCCF),
///         _ => None,
///     }
/// }
/// ```
#[proc_macro_derive(JustMatch)]
pub fn derive_just_match_fn(input: TokenStream) -> TokenStream {
    let ast: DeriveInput = syn::parse(input).unwrap();
    let name = ast.ident;

    let mut members: Vec<(Vec<u8>, TokenStream2)> = vec![];

    if let syn::Data::Enum(data) = ast.data {
        for variant in data.variants {
            let name = variant.ident.to_string();
            members.push((
                name.clone().as_bytes().to_vec(),
                name.parse::<TokenStream2>().unwrap(),
            ));
        }
    }

    let lowercase_name = name.to_string().to_lowercase();
    let fn_name = ("just_match_".to_string() + &lowercase_name)
        .parse::<TokenStream2>()
        .unwrap();

    let mut cases = quote! {};
    for arr in &members {
        let member_name = &arr.1;
        let name_string = format!("\"{}\"", member_name.to_owned())
            .parse::<TokenStream2>()
            .unwrap();
        cases = quote! {
            #cases
            #name_string => Some(#name::#member_name),
        };
    }

    let ret = quote! {
        #[inline(never)] // TODO, just for testing
        fn #fn_name(s: &str) -> Option<#name> {
            match s {
                #cases
                _ => None
            }
        }
    };
    ret.into()
}

/// Turn a match expression on a String into a match on arrays of bytes
/// # Example
/// ```
/// #[derive(comptime_trie::ArrayMatch, Debug, PartialEq)]
/// enum Names {
///     FOO,
///     BAR,
///     BLUB,
///     Z,
///     AAB,
///     CCCA,
///     CCCB,
///     CCCF,
/// }
///
/// assert_eq!(Some(Names::FOO), array_match_names("FOO"));
/// ```
///
/// # Generated Code
///
/// ```
/// # enum Names {
/// #     FOO,
/// #     BAR,
/// #     BLUB,
/// #     Z,
/// #     AAB,
/// #     CCCA,
/// #     CCCB,
/// #     CCCF,
/// # }
///
/// const fn array_match_names(s: &str) -> Option<Names> {
///    match s.as_bytes() {
///        [70u8, 79u8, 79u8] => Some(Names::FOO),
///        [66u8, 65u8, 82u8] => Some(Names::BAR),
///        [66u8, 76u8, 85u8, 66u8] => Some(Names::BLUB),
///        [90u8] => Some(Names::Z),
///        [65u8, 65u8, 66u8] => Some(Names::AAB),
///        [67u8, 67u8, 67u8, 65u8] => Some(Names::CCCA),
///        [67u8, 67u8, 67u8, 66u8] => Some(Names::CCCB),
///        [67u8, 67u8, 67u8, 70u8] => Some(Names::CCCF),
///        _ => None,
///    }
/// }
/// ```
#[proc_macro_derive(ArrayMatch)]
pub fn derive_match_array_fn(input: TokenStream) -> TokenStream {
    let ast: DeriveInput = syn::parse(input).unwrap();
    let name = ast.ident;

    let mut members: Vec<(Vec<u8>, TokenStream2)> = vec![];

    if let syn::Data::Enum(data) = ast.data {
        for variant in data.variants {
            let name = variant.ident.to_string();
            members.push((
                name.clone().as_bytes().to_vec(),
                name.parse::<TokenStream2>().unwrap(),
            ));
        }
    }

    let lowercase_name = name.to_string().to_lowercase();
    let fn_name = ("array_match_".to_string() + &lowercase_name)
        .parse::<TokenStream2>()
        .unwrap();

    let mut cases = quote! {};
    for arr in &members {
        let new_match = {
            let first_elem = arr.0[0];
            let mut ret = quote! {
                #first_elem
            };
            for c in &arr.0[1..] {
                ret = quote! {
                    #ret , #c
                }
            }
            quote! { [ #ret ]}
        };
        let member_name = &arr.1;
        cases = quote! {
            #cases
            #new_match => Some(#name::#member_name),
        };
    }

    let ret = quote! {
        #[inline(never)] // TODO, just for testing
        const fn #fn_name(s: &str) -> Option<#name> {
            match s.as_bytes() {
                #cases
                _ => None
            }
        }
    };
    ret.into()
}
/// Derive a full trie and return the corresponding match statement
/// # Example
/// ```
/// #[derive(comptime_trie::FullTrieMatch, Debug, PartialEq)]
/// enum Names {
///     FOO,
///     BAR,
///     BLUB,
///     Z,
///     AAB,
///     CCCA,
///     CCCB,
///     CCCF,
/// }
///
/// assert_eq!(Some(Names::FOO), full_trie_match_names("FOO"));
/// ```
///
/// # Generated Code
///
/// ```
/// # enum Names {
/// #     FOO,
/// #     BAR,
/// #     BLUB,
/// #     Z,
/// #     AAB,
/// #     CCCA,
/// #     CCCB,
/// #     CCCF,
/// # }
///
/// const fn full_trie_match_names(s: &str) -> Option<Names> {
///     let bytes = s.as_bytes();
///     let s_len = s.len();
///     match bytes[0usize] {
///         65u8 => match s_len == 3usize {
///             true => Some(Names::AAB),
///             false => None,
///         },
///         66u8 => match bytes[1usize] {
///             65u8 => match s_len == 3usize {
///                 true => Some(Names::BAR),
///                 false => None,
///             },
///             76u8 => match s_len == 4usize {
///                 true => Some(Names::BLUB),
///                 false => None,
///             },
///             _ => None,
///         },
///         67u8 => match bytes[1usize] {
///             67u8 => match bytes[2usize] {
///                 67u8 => match bytes[3usize] {
///                     65u8 => match s_len == 4usize {
///                         true => Some(Names::CCCA),
///                         false => None,
///                     },
///                     66u8 => match s_len == 4usize {
///                         true => Some(Names::CCCB),
///                         false => None,
///                     },
///                     70u8 => match s_len == 4usize {
///                         true => Some(Names::CCCF),
///                         false => None,
///                     },
///                     _ => None,
///                 },
///                 _ => None,
///             },
///             _ => None,
///         },
///         70u8 => match s_len == 3usize {
///             true => Some(Names::FOO),
///             false => None,
///         },
///         90u8 => match s_len == 1usize {
///             true => Some(Names::Z),
///             false => None,
///         },
///         _ => None,
///     }
/// }
/// ```
#[proc_macro_derive(FullTrieMatch)]
pub fn derive_safe_match_fn(input: TokenStream) -> TokenStream {
    let ast: DeriveInput = syn::parse(input).unwrap();

    let mut members = vec![];

    if let syn::Data::Enum(data) = ast.data {
        for variant in data.variants {
            members.push(variant.ident);
        }
    }

    let name = ast.ident;

    members.sort_by(|a, b| {
        let mut a = a.to_string();
        let mut b = b.to_string();
        //  TODO this does not work for cases with r#ident??
        if a.starts_with("r#") {
            a = a[2..].to_string();
        }

        if b.starts_with("r#") {
            b = b[2..].to_string();
        }
        a.cmp(&b)
    });

    let alternatives: Vec<(String, TokenStream2, usize)> = members
        .iter()
        .map(|s| s.to_string())
        .map(|s| {
            let len = s.as_bytes().len();
            let enum_variant = s.parse::<TokenStream2>().unwrap();
            let token = quote! { #name::#enum_variant };
            (s, token, len)
        })
        .collect();

    let cases = match_rest(alternatives, 0, true);
    let lowercase_name = name.to_string().to_lowercase();
    let fn_name = ("full_trie_match_".to_string() + &lowercase_name)
        .parse::<TokenStream2>()
        .unwrap();
    return quote! {
        #[inline(never)] // TODO, just for testing
        const fn #fn_name(s: &str) -> Option<#name> {
            let bytes = s.as_bytes();
            let s_len = s.len();

            #cases
        }
    }
    .into();
}

/// # A way to match trusted input
/// The caller has to assert that the input is one of the enum members
///
/// # Example
/// ```
/// #[derive(comptime_trie::FastMatch, Debug, PartialEq)]
/// enum Names {
///     FOO,
///     BAR,
///     BLUB,
///     Z,
///     AAB,
///     CCCA,
///     CCCB,
///     CCCF,
/// }
///
/// assert_eq!(Names::FOO, unsafe { fast_match_names("FOO") });
/// ```
///
/// # Generated Code
/// ```
/// # enum Names {
/// #     FOO,
/// #     BAR,
/// #     BLUB,
/// #     Z,
/// #     AAB,
/// #     CCCA,
/// #     CCCB,
/// #     CCCF,
/// # }
///
/// unsafe fn fast_match_names(s: &str) -> Names {
///     let bytes = s.as_bytes();
///     match bytes.get_unchecked(0usize) {
///         65u8 => Names::AAB,
///         66u8 => match bytes.get_unchecked(1usize) {
///             65u8 => Names::BAR,
///             76u8 => Names::BLUB,
///             _ => std::hint::unreachable_unchecked(),
///         },
///         67u8 => match bytes.get_unchecked(3usize) {
///             65u8 => Names::CCCA,
///             66u8 => Names::CCCB,
///             70u8 => Names::CCCF,
///             _ => std::hint::unreachable_unchecked(),
///         },
///         70u8 => Names::FOO,
///         90u8 => Names::Z,
///         _ => std::hint::unreachable_unchecked(),
///     }
/// }
/// ```
#[proc_macro_derive(FastMatch)]
pub fn derive_fast_match_fn(input: TokenStream) -> TokenStream {
    // Parse the tokens into a syntax tree
    let ast: DeriveInput = syn::parse(input).unwrap();

    let mut members = vec![];

    if let syn::Data::Enum(data) = ast.data {
        for variant in data.variants {
            members.push(variant.ident);
        }
    }

    let name = ast.ident;

    members.sort_by(|a, b| {
        // TODO this does not yet work correclty
        let a = format_ident!("{}", a); // remove r# if present
        let b = format_ident!("{}", b); // remove r# if present
        let a = a.to_string();
        let b = b.to_string();

        a.cmp(&b)
    });
    // dbg!(&members); TODO make sure this works for r# idents/ members

    let alternatives: Vec<(String, TokenStream2, usize)> = members
        .iter()
        .map(|s| s.to_string())
        .map(|s| {
            let len = s.as_bytes().len();
            let enum_variant = s.parse::<TokenStream2>().unwrap();
            let token = quote! { #name::#enum_variant };
            (s, token, len)
        })
        .collect();

    let cases = match_rest(alternatives, 0, false);
    let lowercase_name = name.to_string().to_lowercase();
    let fn_name = ("fast_match_".to_string() + &lowercase_name)
        .parse::<TokenStream2>()
        .unwrap();
    return quote! {
        #[inline(never)] // TODO, just for testing
        unsafe fn #fn_name(s: &str) -> #name {
            let bytes = s.as_bytes();
            #cases
        }
    }
    .into();
}

fn match_rest(
    mut remaining_alternatives: Vec<(String, TokenStream2, usize)>,
    depth: usize,
    safety: bool,
) -> TokenStream2 {
    let mut ret = quote! {};

    let mut chars: Vec<u8> = remaining_alternatives
        .iter()
        .map(|(s, _, _)| s.as_bytes()[0])
        .collect();
    chars.sort_unstable();
    chars.dedup();

    // every byte in the input has to be matched/ checked, even if it is the same in all enum variants
    if !safety {
        // all start with the same char
        if chars.len() == 1 && remaining_alternatives.len() > 1 {
            let new_remaining_alternatives: Vec<(String, TokenStream2, usize)> =
                remaining_alternatives
                    .iter()
                    .map(|(s, t, l)| (s[1..].to_string(), t.clone(), *l))
                    .collect();
            return match_rest(new_remaining_alternatives, depth + 1, safety);
        }
    }

    for &c in &chars {
        let p = remaining_alternatives
            .iter_mut()
            .partition_in_place(|(s, _, _)| s.as_bytes()[0] == c);
        let relevant = &remaining_alternatives[..p];

        let ret_case;
        if relevant.len() == 1 {
            let enum_variant = &relevant[0].1;
            let len = relevant[0].2;

            if safety {
                ret_case = quote! {
                    match s_len == #len {
                       true => Some(#enum_variant),
                       false => None,
                    }
                };
            } else {
                ret_case = quote! {
                    #enum_variant
                };
            }
        } else {
            let new_remaining_alternatives = relevant
                .iter()
                .map(|(s, t, l)| (s[1..].to_string(), t.clone(), *l))
                .collect::<Vec<(String, TokenStream2, usize)>>();
            ret_case = match_rest(new_remaining_alternatives, depth + 1, safety);
        }

        // TODO make this correct when identifier is a r#match, has to skipp the r#
        ret = quote! {
            #ret
            #c => #ret_case,
        };
    }
    if safety {
        quote! {
             match bytes[#depth] {
                #ret
                _ => None,
            }
        }
    } else {
        quote! {
             match bytes.get_unchecked(#depth) {
                #ret
                // _ => unreachable!(), // or just use intrinsic for real unsafety :D
                _ => std::hint::unreachable_unchecked(),
            }
        }
    }
}

// api ideas:

// #[test]
// fn f1(){
//     #[derive(FromArr, PartialEq, Debug)]
//     enum Variants {
//         A([1, 2, 3]),
//         B([1, 2]),
//         C([6, 2, 10, 20]),
//     }
// }

// or

// #[test]
// fn f2() {
//     // #![feature(min_const_generics)]
//     // `inputs` needs to be arrays of size n or smaller,
//     // we need a bound such that we can unroll them at compile time
//     fn create_matcher<T, E, const n: usize>(inputs: &[[T; n]]) -> fn(&[T]) -> E {
//         todo!()
//     }
// }

// function like proc macros would work but would not be very elegant because they cannot be formatted
// so well
