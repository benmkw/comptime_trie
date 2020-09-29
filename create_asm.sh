#! /usr/bin/env bash

for f in just_match_names full_trie_match_names fast_match_names array_match_names
do

    color_f="./output/${f}.txt"
    nocolor_f="./output/${f}_nocolor.txt"

    rustc --version > $color_f
    uname >> $color_f

    rustc --version > $nocolor_f
    uname >> $nocolor_f

    cargo asm proc_test::main::$f --build-type=release --comments --directives >> $color_f
    cargo asm proc_test::main::$f --build-type=release --no-color --comments --directives >> $nocolor_f
done
