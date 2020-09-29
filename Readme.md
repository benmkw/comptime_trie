# comptime_trie

A crate to experiment with different ways of converting strings into enums.
Used to explore what the compiler can do when ones specifies what kinds of strings are expected.
Use `create_asm.sh` to use `cargo asm` to see the generated code for your current rust compiler in the `output` folder.

Use `cargo doc --document-private-items --no-deps --open` to look at examples and generated code.

This could be extended to convert any compile time known set of types which can be converted to an array into a set of corresponding variants/ an enum but I did not come up with a good rust API for that yet. If you have suggestions I'd be interested!

Prior work includes [cttrie](https://smilingthax.github.io/slides/cttrie/).

I [tried to do a similar thing in zig](https://gist.github.com/benmkw/4c3d04ec87dd7668e4af972d5ae6971b) but failed because allocating during compile time in stage one is not super well supported and will wait for stage2 (self hosted) and try it again.

Alternative approaches include [perfect hashing](https://andrewkelley.me/post/string-matching-comptime-perfect-hashing-zig.html).

Thanks to eddyb on zulip for the idea to try sice patterns, errors in the code are mine of course ;)

You can't use this as a library yet because I have `#[inline(never)]` calls in there and because this was only used to see what the compiler does to the code I have not bothered yet to remove them/ make them optional.

The shortest output is produced by:
(it trusts the input though and has undefined behaviour if the input does not match one of the enum variants thus I'm not sure if this is ever usefull)

```rust
#[derive(comptime_trie::FastMatch, Debug, PartialEq)]
enum Names {
    FOO,
    BAR,
    BLUB,
    Z,
    AAB,
    CCCA,
    CCCB,
    CCCF,
}
assert_eq!(Names::FOO, unsafe { fast_match_names("FOO") });

//  Generated Code
// you can notably see that it never checks index 1 or 2 if pos 0 is a C
// thus in theory this version can be "arbitraily" faster than memcompare, depending on the enum members ;)
unsafe fn fast_match_names(s: &str) -> Names {
    let bytes = s.as_bytes();
    match bytes.get_unchecked(0usize) {
        65u8 => Names::AAB,
        66u8 => match bytes.get_unchecked(1usize) {
            65u8 => Names::BAR,
            76u8 => Names::BLUB,
            _ => std::hint::unreachable_unchecked(),
        },
        67u8 => match bytes.get_unchecked(3usize) {
            65u8 => Names::CCCA,
            66u8 => Names::CCCB,
            70u8 => Names::CCCF,
            _ => std::hint::unreachable_unchecked(),
        },
        70u8 => Names::FOO,
        90u8 => Names::Z,
        _ => std::hint::unreachable_unchecked(),
    }
}
```

```asm
rustc 1.48.0-nightly (d006f5734 2020-08-28)
Darwin
proc_test::main::fast_match_names:
 push    rbp
 .cfi_def_cfa_offset 16
 .cfi_offset rbp, -16
 mov     rbp, rsp
 .cfi_def_cfa_register rbp
 mov     cl, byte, ptr, [rdi]
 mov     al, 4
 add     cl, -65
 movzx   ecx, cl
 lea     rdx, [rip, +, LJTI18_0]
 movsxd  rcx, dword, ptr, [rdx, +, 4*rcx]
 add     rcx, rdx
 jmp     rcx
LBB18_2:
 cmp     byte, ptr, [rdi, +, 1], 65
 sete    cl
 mov     al, 2
 sub     al, cl
 pop     rbp
 ret
LBB18_8:
 xor     eax, eax
 pop     rbp
 ret
LBB18_3:
 mov     al, byte, ptr, [rdi, +, 3]
 cmp     al, 65
 je      LBB18_4
 cmp     al, 66
 je      LBB18_6
 mov     al, 7
 pop     rbp
 ret
LBB18_9:
 mov     al, 3
LBB18_10:
 pop     rbp
 ret
LBB18_4:
 mov     al, 5
 pop     rbp
 ret
LBB18_6:
 mov     al, 6
 pop     rbp
 ret
LBB18_1:
 ud2
```
