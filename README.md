# Snakepiler

A compiler created by [@connernilsen](https://github.com/connernilsen) and [@kinto0](https://github.com/kinto0)!

## Features
- Python-like syntax
- An expression based language
- Sequencing
- Recursion
- Garbage collection
- Strong dynamic typing
- First-class functions
- Built-in numbers, booleans, strings, tuples, 
- Let bindings
- Reading from stdin/writing to stdout
- Compilation to x86_64 assembly
- C runtime for support functionality
- String and list library

## Setup

1. Install [OPAM](https://opam.ocaml.org/) (make sure you have at least v2.1.2)
  - Note: using Homebrew is easiest if possible
2. Install a switch for OCaml by running `opam switch create 4.13.1`
3. Install required packages `opam install extlib ounit batteries utop`
4. Make sure the following APT packages are installed: `clang, nasm, valgrind, bubblewrap, m4`

## Building Snakey

To build Snakey, run `make main` from the current directory. The final executable should be available in the current directory as `main`.

To build the main executable and test executable, run `make test` in the current directory. The test executable should be made available as `test` in the current directory. 

Since each of the tests need to be removed before re-running `./test`, another Makefile command has been created to cache useful files for repeated tests. Run `make ct` to remove unnecessary tempfiles and rebuild both the main and test executables using cached resources.

## Running Snakey

To run the main executable, provide the location of the source file as a parameter. For example, `./main myfile.sn`. The following options are also available
- `-t`: enable a trace of the compilation process, showing the output produced by each stage of the compiler
- `-d`: enable debug output
- `-alloc <strategy>`: use the given binding allocation strategy (options are `stack` and `register`)
