#!/usr/bin/env python3

if __name__ == '__main__':
  import os
  import sys

  esbmc_slhv_root = "./esbmc/"
  esbmc_slhv_build = esbmc_slhv_root + "build/"
  esbmc_slhv = esbmc_slhv_build + "src/esbmc/esbmc"

  if sys.argv[1] == "--compile":
    os.system(f"cd {esbmc_slhv_build } && cmake --build .")
  elif sys.argv[1] == "--run":
    cprog = sys.argv[2]
    assert(os.path.exists(cprog))

    output_file = "vcc.log"

    args = [
      cprog,
      "--no-library",
      "--ir",
      "--force-malloc-success",
      "--memory-leak-check",
      "--ssa-smt-trace",
      "--result-only",
      "--show-vcc",
      "--output",
      output_file
    ]

    if "--bv" not in sys.argv : args.append("--z3-slhv")
    if "--multi" in sys.argv : args.append("--multi-property") 
    if "--no-slice" in sys.argv : args.append("--no-slice")  

    os.system(esbmc_slhv + " " + " ".join(args))
  elif sys.argv[1] == "--help":
    os.system(f"{esbmc_slhv} -h")
  else:
    assert(False)
