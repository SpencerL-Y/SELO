## SELO

SELO is a bounded model checking framework for checking memory safety properties in heap-manipulating C programs.
It inherits the architecture of [ESBMC](https://github.com/esbmc/esbmc) and components needed for BMC upon  Seperation Logic with Heap Variables(SLHV) are added into the framework.
SELO encodes verification conditions(VCs) in SLHV and such VC will be fed to [Z3-SLHV](https://anonymous.4open.science/r/Z3-SLHV) to solve.

## Building SELO

SELO shares the same building method with ESBMC, one can refer to ESBMC for detailed information. 
For convenience, we give some scripts and commands to compile the target.
### Prerequisite
Linux:
```
sudo apt-get update && sudo apt-get install build-essential git gperf libgmp-dev cmake bison curl flex g++-multilib linux-libc-dev libboost-all-dev libtinfo-dev ninja-build python3-setuptools unzip wget python3-pip openjdk-8-jre
```
CMake > 3.22

### Alternative 1: Building with shared library
#### preparing Clang
**Preparing distributed Clang (recommended for a shared build)**
For shared builds, it is recommended to use the system's LLVM/Clang, which on Ubuntu can be obtained by:
```
apt-get install libclang-cpp11-dev &&
ESBMC_CLANG="-DLLVM_DIR=/usr/lib/llvm-11/lib/cmake/llvm -DClang_DIR=/usr/lib/cmake/clang-11" &&
ESBMC_STATIC=OFF
```
#### Setting up solvers
referring to [Z3-SLHV](https://anonymous.4open.science/r/Z3-SLHV)

#### Compile SELO
Before running the following commands, make sure ```your_z3_lib_path``` and ```your_release_path``` are configured in the script file ```mk_make.py```.
```
mkdir build
python3 mk_make.py --shared
```

### Alternative 2: Building with static library

#### preparing Clang
**Preparing external standard Clang (recommended for a static build)**

You can either download and unpack a release manually:
```
wget https://github.com/llvm/llvm-project/releases/download/llvmorg-11.0.0/clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz &&
tar xfJ clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz &&
ESBMC_CLANG=$(echo -D{LLVM,Clang}_DIR=$PWD/clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04) &&
ESBMC_STATIC=ON
```
#### Setting up solvers
referring to [Z3-SLHV](https://anonymous.4open.science/r/Z3-SLHV)

#### Compile SELO
Before running the following commands, make sure ```your_z3_lib_path``` and ```your_release_path``` are configured in the script file ```mk_make.py```.
```
mkdir build
python3 mk_make.py --static
```
