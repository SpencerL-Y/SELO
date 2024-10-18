# SELO

SELO is a bounded model checking framework for checking memory safety properties in heap-manipulating C programs.
It inherits the architecture of [ESBMC](https://github.com/esbmc/esbmc) and components needed for BMC upon  Separation Logic with Heap Variables(SLHV) are added into the framework.
SELO encodes verification conditions(VCs) in SLHV and such VC will be fed to [Z3-SLHV](https://anonymous.4open.science/r/Z3-SLHV).

## Building

SELO shares the same building method with ESBMC, one can refer to [BUILDING](./docs/ESBMC_BUILDING.md) of ESBMC for detailed information.

For convenience, we give some scripts and commands to compile the target.

### Using script(recommended)

We provide a script `./scripts/build.sh` to automatically configure LLVM and Z3-SLHV and compile SELO.
```sh
./scripts/build.sh
```
More detail can be found by `-h`.

*Notice: the script must be executed in root of SELO.*

### Manually building

#### Prerequisite
Linux:
```
sudo apt-get update && sudo apt-get install build-essential git gperf libgmp-dev cmake bison curl flex g++-multilib linux-libc-dev libboost-all-dev libtinfo-dev ninja-build python3-setuptools unzip wget python3-pip openjdk-8-jre
```
CMake >= 3.22

#### Alternative 1: Building with shared library

**Preparing distributed Clang (recommended for a shared build)**

For shared builds, it is recommended to use the system's LLVM/Clang, which on Ubuntu can be obtained by:
```
apt-get install libclang-cpp11-dev &&
ESBMC_CLANG="-DLLVM_DIR=/usr/lib/llvm-11/lib/cmake/llvm -DClang_DIR=/usr/lib/cmake/clang-11" &&
ESBMC_STATIC=OFF
```

**Preparing distributed Z3-SLHV (recommended for a shared build):**
Referring to [Z3-SLHV](https://anonymous.4open.science/r/Z3-SLHV)

**Configuring CMake**
```sh
mkdir build && cd build
cmake .. -GNinja -DClang_DIR=/usr/lib/cmake/clang-11 \
  -DLLVM_DIR=/usr/lib/llvm-11/lib/cmake/llvm \
  -DENABLE_Z3_SLHV=On \
  -DZ3_DIR=<path_to_Z3-SLHV>/z3_slhv_lib
```

#### Alternative 2: Building with static library

**Preparing external standard Clang (recommended for a static build)**

You can either download and unpack a release manually:
```
wget https://github.com/llvm/llvm-project/releases/download/llvmorg-11.0.0/clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz &&
tar xfJ clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz &&
ESBMC_CLANG=$(echo -D{LLVM,Clang}_DIR=$PWD/clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04) &&
ESBMC_STATIC=ON
```
**Preparing distributed Z3-SLHV (recommended for a static build):**
Referring to [Z3-SLHV](https://anonymous.4open.science/r/Z3-SLHV)

**Configuring CMake**
```sh
mkdir build && cd build
cmake .. -GNinja -DClang_DIR=<path_to_cmake/clang-11>
  -DLLVM_DIR=<path_to_llvm-11/lib/cmake/llvm> \
  -DBUILD_STATIC=ON \
  -DENABLE_Z3_SLHV=On \
  -DZ3_DIR=<path_to_Z3-SLHV>/z3_slhv_lib
```
Note that all `path_to_*` must be configured correctly. More details can be found in ESBMC.

#### Compile SELO

```sh
cd build && cmake --build .
```
If compiler can not find `z3++.h`, appending arg `
 -DCMAKE_CXX_FLAGS="-I<path_to_Z3-SLHV>/z3_slhv_lib/include"` solves the issue.

## Running SELO

To run SELO, the following arguments must be included.
```sh
--no-library --force-malloc-success --result-only --multi-property --z3-slhv
```
`--z3-slhv` is a must to enable SELO using SLHV for encoding and using Z3-SLHV for backend solver.

We also provide a simple script `x.py`. We can easily to run SELO on a single file. For example, we run SELO on "case_1.c" in our benchmark bu the following command.
```sh
./x.py --run ./benchmark/tests/case_1.c
```
Output of SELO will be stored in `./output/t.log`. More details can be found by `./x.py --help`.

For further utilizing, we recommend that a new working directory should be created and `x.py` should be copied into the directory. Moreover, the root of SELO in the scripts must be set correctly

## Open source and License

SELO is an open-source software mainly distributed under the Apache License 2.0. It is based on ESBMC. Most of codes of ESBMC are preserved. Please take a look at the COPYING file to explain who owns what and under what terms it is distributed. The files BUILDING, CITATION, CREDITS and COPYING are preserved in `docs`. Thanks for the contributions of the authors of ESBMC.