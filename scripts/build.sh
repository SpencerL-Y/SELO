#!/bin/sh

# Set arguments
BASE_ARGS="-GNinja"

SOLVER_FLAGS="-DENABLE_Z3_SLHV=On"

COMPILER_ARGS=''

STATIC=
CLANG_VERSION=11

error() {
    echo "error: $*" >&2
    exit 1
}

# Ubuntu setup (pre-config)
ubuntu_setup () {
    
    # Tested on ubuntu 22.04
    PKGS="\
        python-is-python3 csmith python3 \
        git ccache unzip wget curl libcsmith-dev gperf \
        libgmp-dev cmake bison flex g++-multilib linux-libc-dev \
        libboost-all-dev ninja-build python3-setuptools \
        libtinfo-dev pkg-config python3-pip python3-toml \
        openjdk-11-jdk \
    "

    # Create deps for Clang and Z3_SLHV
    if [ ! -d "deps" ]; then
        echo "Create deps directory"
        mkdir deps
    fi
    cd deps
    DEPS_ROOT=$PWD

    
    if [ -z "$STATIC" ]; then
        STATIC=ON
        echo "Static building"
    else
        echo "Shared building"
    fi

    echo "Configuring Clang-$CLANG_VERSION"
    if [ $STATIC = OFF ]; then
        PKGS="$PKGS \
            llvm-$CLANG_VERSION-dev \
            libclang-$CLANG_VERSION-dev \
            libclang-cpp$CLANG_VERSION-dev \
        "
        BASE_ARGS="$BASE_ARGS \
            -DClang_DIR=/usr/lib/cmake/clang-$CLANG_VERSION \
            -DLLVM_DIR=/usr/lib/llvm-$CLANG_VERSION/lib/cmake/llvm \
        "
    else
        if [ ! -d "clang+llvm-11" ]; then
            wget https://github.com/llvm/llvm-project/releases/download/llvmorg-11.0.0/clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz
            tar xfJ clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04.tar.xz
            mv clang+llvm-11.0.0-x86_64-linux-gnu-ubuntu-20.04 clang+llvm-11
        fi
        BASE_ARGS="$BASE_ARGS -DClang_DIR=$PWD/clang+llvm-11 -DLLVM_DIR=$PWD/clang+llvm-11"
    fi


    echo "Configuring Z3_SLHV"
    if [ ! -d "Z3-SLHV" ]; then
        git clone https://github.com/SpencerL-Y/Z3-SLHV.git
    fi
    cd Z3-SLHV
    if [ ! -d "z3_slhv_lib" ]; then
        rm -r build && python3 mk_${STATIC}_cmake.py
        cd build && ninja install
    fi
    cd $DEPS_ROOT/Z3-SLHV
    BASE_ARGS="$BASE_ARGS -DBUILD_STATIC=$STATIC"
    SOLVER_FLAGS="$SOLVER_FLAGS \
        -DZ3_DIR=$PWD/z3_slhv_lib \
        -DCMAKE_CXX_FLAGS=\"-I$PWD/z3_slhv_lib/include\" \
    "
    
    sudo apt-get update &&
    sudo apt-get install -y $PKGS &&
    echo "Installing Python dependencies" &&
    pip3 install --user meson ast2json &&
    meson --version
}

usage() {
    echo "$0 [-OPTS]"
    echo
    echo "THe script should be executed in ./script/"
    echo "Options [defaults]:"
    echo "  -h         display this help message"
    echo "  -b BTYPE   set cmake build type to BTYPE [RelWithDebInfo]"
    echo "  -c         enable clang [disabled]"
    echo "  -e ON|OFF  enable/disable -Werror [OFF]"
    echo "  -S ON|OFF  enable/disable static build [ON]"
    echo
    echo "This script prepares the environment, downloads dependencies, configures"
    echo "the SELO build and runs the commands to compile."
    echo
    echo "Supported environments: Ubuntu-22.04"
}

# Setup build flags (release, debug, sanitizer, ...)
while getopts hb:s:e:r:dS:c:CB: flag
do
    case "${flag}" in
    h) usage; exit 0 ;;
    b) BASE_ARGS="$BASE_ARGS -DCMAKE_BUILD_TYPE=${OPTARG}" ;;
    s) BASE_ARGS="$BASE_ARGS -DSANITIZER_TYPE=${OPTARG}"
       COMPILER_ARGS="$COMPILER_ARGS CC=clang CXX=clang++" ;;
    e) BASE_ARGS="$BASE_ARGS -DENABLE_WERROR=${OPTARG}" ;;
    S) STATIC=$OPTARG ;; # should be capital ON or OFF
    *) exit 1 ;;
    esac
done
if [ $# -ge $OPTIND ]; then
    shift $((OPTIND-1))
    error "unknown trailing parameters: $*"
fi

ROOT=$PWD
if [ `basename $ROOT` != "SELO" ]; then
    error "The script must be executed in root of SELO"
fi

# Setup Clang+LLVM and Z3_SLHV
ubuntu_setup

echo "Build SELO"
cd $ROOT

# Create build directory
if [ ! -d "build" ]; then
    mkdir build
fi
cd build && rm -rf *

printf "Running CMake:"
printf " '%s'" $COMPILER_ARGS cmake .. $BASE_ARGS $SOLVER_FLAGS
echo
$COMPILER_ARGS cmake .. $BASE_ARGS $SOLVER_FLAGS

# Compile SELO
cmake --build .
