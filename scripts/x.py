#!/usr/bin/env python3

import os
import sys
import csv

esbmc_slhv_root = "./esbmc"
esbmc_slhv_build = os.path.join(esbmc_slhv_root, "build")
esbmc_slhv = os.path.join(esbmc_slhv_build, "src", "esbmc", "esbmc")

output_root = "./output"
log_root = os.path.join(output_root, "Logs")
vcc_root = os.path.join(output_root, "VCCs")
t_log = os.path.join(output_root, "t.log")
vcc_log = os.path.join(output_root, "vcc.log")

csv_file = os.path.join(output_root, "results.csv")

def compile():
  os.system(f"cd {esbmc_slhv_build } && cmake --build .")

def help():
  os.system(f"{esbmc_slhv} -h")

def collect_one_assert(info):
  assert(len(info) == 3)
  res = {}
  
  # Location
  res["Line"] = "None"
  res["Column"] = "None"
  if len(info[0].split(' ')) >= 7:
    location = info[0].split(' ')
    res["Line"] = location[4]
    res["Column"] = location[6]

  # Property & Result & Time
  prt = info[2].split(" ")
  res["Property"] = prt[1]
  res["Result"] = prt[3]
  res["Time"] = prt[5].replace('s', '')

  return res

def analysis_result(log):
  assert(os.path.exists(log))

  flag = "--- Result ---"
  
  assert_results = []
  total_time = 0
  is_collecting = False
  with open(log) as log_file:
    info_buf = []
    for line in log_file:
      if line.find(flag) != -1:
        if not is_collecting:
          is_collecting = True
          continue
        else:
          is_collecting = False
          one_res = collect_one_assert(info_buf)
          assert_results.append(one_res)
          info_buf.clear()

          # collect time for each assertion
          total_time += float(one_res["Time"])
          
      if not is_collecting: continue
      info_buf.append(line.strip())
  
  return (assert_results, total_time)

def run_on(cprog, extra_args):
  assert(os.path.exists(cprog))
  
  cprog_name = os.path.basename(cprog)
  print(f"Verifying program: {cprog_name}")

  args = [
    esbmc_slhv,
    cprog,
    "--no-library",
    "--ir",
    "--force-malloc-success",
    "--memory-leak-check",
    "--result-only",
    "--show-vcc",
    "--output",
    vcc_log,
    "--multi-property",
    "--z3-slhv"
  ]

  if "--debug" in extra_args:
    args.append("--verbosity SLHV:8")

  redirect_arg = [">", t_log]
  if "--std-out" not in extra_args:
    args += redirect_arg

  cmd = " ".join(args)
  print(f"Command: {cmd}")
  os.system(cmd)
  
  (result, total_time) = analysis_result(t_log)
  for d in result:
    res = [k + ": " + v for k, v in list(d.items())]
    print("{:<10} {:<12} {:<25} {:<15} {:<10}".format(*res))

  print(f"Total time: {round(total_time, 3)}")

  return result

def collect_results(cprog):
  cprog_name = cprog.split('.')[0]

  log_file = cprog_name + "_log.log"
  vcc_file = cprog_name + "_vcc.log"

  log_path = os.path.join(log_root, log_file)
  vcc_path = os.path.join(vcc_root, vcc_file)

  os.system(f"cp {t_log} {log_path}")
  os.system(f"cp {vcc_log} {vcc_path}")

  print(f"Result for {cprog}: {log_path} {vcc_path}")
  

def generate_csv(results):
  print(f"Write to {csv_file}")
  with open(csv_file, "w") as f:
    header = ["File", "Line", "Column", "Property", "Result", "Time"]
    w = csv.DictWriter(f, header)
    w.writeheader()
    for cprog, assert_results in results.items():
      is_head = True
      total_time = 0
      for assert_result in assert_results:
        new_row = {'File': cprog if is_head else ''}
        is_head = False
        total_time += float(assert_result["Time"])
        new_row.update(assert_result)
        w.writerow(new_row)
      new_row = {
        "File": '',
        "Line": '',
        "Column": '',
        "Property": '',
        "Result": 'Totaltime',
        "Time": total_time
      }
      w.writerow(new_row)
    

def run_expriment_on(benchmark_root):
  assert(os.path.exists(benchmark_root))
  
  cprogs = []
  for file in os.listdir(f"{benchmark_root}"):
    if file.endswith(".c"):
      cprogs.append(file)
  
  cprogs = sorted(cprogs)
  
  results = {}
  for cprog in cprogs:
    cprog_path = os.path.join(benchmark_root, cprog)
    results[cprog] = run_on(cprog_path, [])
    collect_results(cprog)

  generate_csv(results)    

if __name__ == '__main__':
  if not os.path.exists(output_root):
    os.mkdir(output_root)
  if not os.path.exists(log_root):
    os.mkdir(log_root)
  if not os.path.exists(vcc_log):  
    os.mkdir(vcc_root)

  if sys.argv[1] == "--compile":
    compile()
  elif sys.argv[1] == "--run":
    run_on(sys.argv[2], sys.argv[3:])
  elif sys.argv[1] == "--experiment":
    run_expriment_on(sys.argv[2])
  elif sys.argv[1] == "--help":
    help()
  else:
    assert(False)