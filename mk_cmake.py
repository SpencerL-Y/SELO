import os
import sys

os.system("cd build && rm -rf * && cmake .. -GNinja -DBUILD_TESTING=On -DENABLE_REGRESSION=On $ESBMC_CLANG  -DENABLE_Z3_SLHV=On -DZ3_DIR=/home/clexma/Desktop/fox3/slhv/Z3-slhv/z3_slhv_lib  -DCMAKE_INSTALL_PREFIX:PATH=$PWD/../../release ")
