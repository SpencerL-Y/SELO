import os
import sys

os.system("cd build && cmake .. -GNinja -DBUILD_TESTING=On -DENABLE_REGRESSION=On $ESBMC_CLANG  -DENABLE_Z3=On -DZ3_DIR=/../../../z3-release  -DCMAKE_INSTALL_PREFIX:PATH=$PWD/../../release ")
