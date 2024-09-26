#!/usr/bin/env python3

import argparse
from enum import Enum
import shlex
import subprocess
import sys

esbmc_slhv = "./esbmc_slhv "
default_args = "--no-library --ir --force-malloc-success --result-only --multi-property --z3-slhv"

class Property(Enum):
  memory = 1
  memcleanup = 2

class Result(Enum):
  success = 1
  fail_deref = 2
  fail_free = 3
  fail_memtrack = 4
  fail_memcleanup = 5
  unknown = 6

def analysis_result(out, prop):

  log = out.decode()
  
  invalid_deref = "Property: INVALID_DEREF Result: sat"
  invalid_free = "Property: INVALID_FREE Result: sat"
  memory_leak = "Property: MEMORY_LEAK Result: sat"
  
  if "VERIFICATION FAILED":
    if prop == Property.memory:
      if invalid_deref in log:
        return Result.fail_deref
      if invalid_free in log:
        return Result.fail_free
      if memory_leak in log:
        return Result.fail_memtrack

    if prop == Property.memcleanup:
      if memory_leak in log:
        return Result.fail_memcleanup

  if "VERIFICATION SUCCESSFUL" in log:
    return Result.success

  return Result.unknown

def do_exec(cmd_line):
  the_args = shlex.split(cmd_line)
  p = subprocess.Popen(the_args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  (stdout, stderr) = p.communicate()
  return stdout + stderr

def run(cmd_line):
  print("Verifying with ESBMC_SLHV")
  print("Command: " + cmd_line)
  out = do_exec(cmd_line)
  print(out.decode())
  return out

def mk_cmd(benchmark, prop):
  cmd = esbmc_slhv + benchmark + " " + default_args
  if prop == Property.memory:
    cmd += " --memory-leak-check"
  elif prop == Property.memcleanup:
    cmd += "--no-pointer-check --no-bounds-check --memory-leak-check"
  return cmd

def verify(benchmark, property):
  cmd = mk_cmd(benchmark, property)
  out = run(cmd)
  return analysis_result(out, property)

def get_result_string(the_result):
  if the_result == Result.fail_memcleanup:
    return "FALSE_MEMCLEANUP"

  if the_result == Result.fail_memtrack:
    return "FALSE_MEMTRACK"

  if the_result == Result.fail_free:
    return "FALSE_FREE"

  if the_result == Result.fail_deref:
    return "FALSE_DEREF"

  if the_result == Result.success:
    return "TRUE_PROP"

  if the_result == Result.unknown:
    return "UNKNOWN"

  exit(0)

if __name__ == '__main__':
  
  parser = argparse.ArgumentParser()
  parser.add_argument("benchmark", nargs='?', help="Path to the benchmark")
  parser.add_argument("-v", "--version", help="Print version", action='store_true')
  parser.add_argument("-p", "--propertyfile", help="Path to the property file")

  args = parser.parse_args()
  property_file = args.propertyfile
  benchmark = args.benchmark

  # if property_file is None:
  #   print("Please, specify a property file")
  #   exit(1)

  if benchmark is None:
    print("Please, specify a benchmark to verify")
    exit(1)

  # Parse property files
  # f = open(property_file, 'r')
  # property_file_content = f.read()

  property = Property.memory
  # if "CHECK( init(main()), LTL(G valid-free) )" in property_file_content:
  #   property = Property.memory
  # elif "CHECK( init(main()), LTL(G valid-memcleanup) )" in property_file_content:
  #   property = Property.memcleanup
  # else:
  #   print("Unsupported Property")
  #   exit(1)
  
  result = verify(benchmark, property)
  print(get_result_string(result))