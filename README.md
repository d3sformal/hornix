# Hornix

## **Getting started**

#### Dependencies

To build `Hornix`, you need `LLVM` installation discoverable by `CMake`.
It is useful to provide CMake with a path to the directory with LLVM's CMake config using `-DLLVM_DIR=<your_path>`.

*Note:* This will most likely be `<LLVM_INSTALL_DIR>/lib/cmake/llvm`, where `<LLVM_INSTALL_DIR>` is the directory of LLVM, either the installation or the main repository directory (if you are buildiing from source).
For example, when llvm is installed with homebrew, the path could be `/opt/homebrew/Cellar/llvm/20.1.2/`



To build `Hornix` run the following in the repository root:
```shell
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DLLVM_DIR=<path_to_llvm_cmake_config_dir>
cmake --build build
```

This will create the `hornix` executable in `build/src`.


## **Using Hornix**

Hornix currently accepts LLVM's IR textual representation, i.e., `.ll` files.
To obtain `.ll` file from C file, you can use `clang 18` or higher:
```shell
clang -Xclang -disable-O0-optnone -S -emit-llvm {source code} -o {output file}
```

Then you can run `Hornix`

For example, source code file *example.cpp* :

```
clang -Xclang -disable-O0-optnone -S -emit-llvm example.cpp -o example.ll

build/src/hornix example.ll 
```

`Hornix` uses `Z3` as the backend and it expects `Z3` binary is available on your PATH.

### Integer encodings

By default, Hornix retains its original unbounded-integer encoding:

```shell
build/src/hornix example.ll
```

Use `--integer-theory bitvectors` to encode LLVM `iN` values (`N > 1`) as
fixed-width SMT-LIB bit-vectors; `i1` remains a Boolean. This preserves modular
arithmetic, signed and unsigned comparisons, division/remainder, bitwise
operations, shifts, and integer casts.

```shell
build/src/hornix --integer-theory bitvectors example.ll
```

### Violation witnesses

Hornix can emit a YAML 2.2 violation witness for an unsafe `unreach-call`
task.  The witness mode currently supports a single `.c` input, the
bit-vector encoding, and either SV-COMP C data model (`ILP32` or `LP64`).

```shell
build/src/hornix \
  --integer-theory bitvectors \
  --data-model LP64 \
  --property path/to/unreach-call.prp \
  --witness-format 2.1 \
  --witness-output result.witness.yml \
  program.c
```

The witness is written only when Hornix reports `unsat` (an error is
reachable in Hornix's CHC encoding).  It contains the required task metadata,
the SHA-256 hash of the physical source input, and a `target` waypoint for the
direct call named by the property.  To prevent an arbitrary target being
reported, the current implementation requires that this call can be located
unambiguously in the original source; macros and several calls to the target
are rejected.  Reconstructing a path and nondeterministic choices from Z3 is
not implemented yet.

The default format is 2.2. Use `--witness-format 2.0` or
`--witness-format 2.1` for validators that do not yet support 2.2; CPAchecker
4.2.2 accepts version 2.1.
