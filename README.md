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
clang++ -Xclang -disable-O0-optnone -S -emit-llvm {source code} -o {output file}
```

Then you can run `Hornix`

For example, source code file *example.cpp* :

```
clang++ -Xclang -disable-O0-optnone -S -emit-llvm example.cpp -o example.ll

build/src/hornix example.ll 
```

`Hornix` uses `Z3` as the backend and it expects `Z3` binary is available on your PATH.
