import os
import sys

your_z3_lib_path = "/home/clexma/Desktop/fox3/slhv/Z3-slhv/z3_slhv_lib"
your_release_path = "$PWD/../../release" 
is_static = sys.argv[1]
if "--static" in  is_static:

    os.system("cd build && rm -rf * && cmake .. -GNinja -DBUILD_TESTING=On -DENABLE_REGRESSION=On $ESBMC_CLANG  -DBUILD_STATIC=${ESBMC_STATIC:-ON} -DENABLE_Z3_SLHV=On -DZ3_DIR=" + your_z3_lib_path + " -DCMAKE_INSTALL_PREFIX:PATH=" + your_release_path)
elif "--shared" in is_static:
    os.system("cd build && rm -rf * && cmake .. -GNinja -DBUILD_TESTING=On -DENABLE_REGRESSION=On $ESBMC_CLANG  -DENABLE_Z3_SLHV=On -DZ3_DIR=" + your_z3_lib_path + "   -DCMAKE_INSTALL_PREFIX:PATH=" + your_release_path)
else:
    print("need argument: --static or --shared")




