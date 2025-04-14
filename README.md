# Hornix

## **Getting started**

#### Dependencies

To build `Hornix`, you need `LLVM` installation discoverable by `CMake`.
It is useful to provide CMake with a path to the directory with LLVM's CMake config using `-DLLVM_DIR=<your_path>`.

To build `Hornix` run the following in the repository root:
```shell
cmake -S . -B build -DCMAKE__BUILD_TYPE=Release -DLLVM_DIR=<path_to_llvm_cmake_config_dir>
cmake --build build
```

This will create the `hornix` executable in `build/src`.


## **Using Hornix**

Hornix currently accepts LLVM's IR textual representation, i.e., `.ll` files.
To obtain `.ll` file from C file, you can use `clang 18` or higher:
```shell
clang++ -Xclang -disable-O0-optnone -S -emit-llvm {source code} -o {output file}
```

Then you can run `Hornix`

For example, source code file *example.cpp* :

```
clang++ -Xclang -disable-O0-optnone -S -emit-llvm example.cpp -o example.ll

build/src/hornix example.ll 
```

`Hornix` uses `Z3` as the backend and it expects `Z3` binary is available on your PATH.