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

  cmds = {
    "--compile" : ('',"Compile esbmc"),
    "--run" : ("file extra_args","Only test a single file 'file'"),
    "--experiment": ("path extra_args", "Run on a benchmark 'path'"),
    "--help": ('', "Show help information"),
  }

  args = {
    "--esbmc" : "Disable SLHV and use default esbmc with solver Z3",
    "--debug" : "Output debug info of SLHV",
    "--std-out" : "Output info in std::out"
  }

  print("Commands for x.py:")
  for cmd in cmds.items():
    cmdline = [cmd[0] + ' ' + cmd[1][0], cmd[1][1]]
    print(" {:<35} {:<50}".format(*cmdline))
  print("Extra args:")
  for arg in args.items():
    print(" {:<35} {:<50}".format(*arg))

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
  formulas = 0
  total_time = 0
  mi_time = float(901)
  mx_time = float(0)
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
          time = float(one_res["Time"])
          total_time += time
          mi_time = min(mi_time, time)
          mx_time = max(mx_time, time)
          formulas += 1
          
      if not is_collecting: continue
      info_buf.append(line.strip())
  
  return (assert_results, formulas, total_time, mi_time, mx_time)

def run_on(cprog, extra_args):
  assert(os.path.exists(cprog))
  
  cprog_name = os.path.basename(cprog)
  print(f"Verifying program: {cprog_name}")

  args = [
    esbmc_slhv,
    cprog,
    "--no-library",
    "--force-malloc-success",
    "--memory-leak-check",
    "--result-only",
    "--show-vcc",
    "--output",
    vcc_log,
    "--multi-property",
    # "--no-slice"
  ]

  if "--esbmc" in extra_args:
    args.append("--z3")
  else:
    args.append("--z3-slhv")

  if "--debug" in extra_args:
    args.append("--verbosity SLHV:8")

  if "--std-out" not in extra_args:
    args += [">", t_log, "2>&1"]

  cmd = " ".join(args)
  print(f"Command: {cmd}")
  os.system(cmd)
  
  (result, formulas, total_time, mi_time, mx_time) = analysis_result(t_log)
  for d in result:
    res = [k + ": " + v for k, v in list(d.items())]
    print("{:<10} {:<12} {:<25} {:<15} {:<10}".format(*res))

  print(f"Formulas: {formulas}, \
        Total time: {round(total_time, 3)}, \
        Average time: {round(total_time / formulas, 3)} \
        Min time: {round(mi_time, 3)}, \
        Max time: {round(mx_time, 3)}")

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
    formulas = [0, 0]
    total_time = [0.0, 0.0]
    mi_time = [-1.0, -1.0]
    mx_time = [-1.0, -1.0]
    for cprog, assert_results in results.items():
      is_head = True
      i_formulas = [0, 0]
      i_total_time = [0.0, 0.0]
      i_mi_time = [-1.0, -1.0]
      i_mx_time = [-1.0, -1.0]
      for assert_result in assert_results:
        new_row = {'File': cprog if is_head else ''}
        is_head = False
        
        time = float(assert_result["Time"])
        r = 0 if assert_result["Result"] == "sat" else 1
        i_formulas[r] += 1
        i_total_time[r] += time

        if i_mi_time[r] == -1.0:
          i_mi_time[r] = time
        else:
          i_mi_time[r] = min(i_mi_time[r], time)
        
        if i_mx_time[r] == -1.0:
          i_mx_time[r] = time
        else:
          i_mx_time[r] = max(i_mx_time[r], time)

        formulas[r] += 1
        total_time[r] += time

        if mi_time[r] == -1.0:
          mi_time[r] = time
        else:
          mi_time[r] = min(mi_time[r], time)
        
        if mx_time[r] == -1.0:
          mx_time[r] = time
        else:
          mx_time[r] = max(mx_time[r], time)

        new_row.update(assert_result)
        w.writerow(new_row)
      
      i_sat_ave = round(i_total_time[0] / i_formulas[0], 3) if i_formulas[0] != 0 else '-'
      i_unsat_ave = round(i_total_time[1] / i_formulas[1], 3)

      mit = ['-', '-']
      mxt = ['-', '-']

      if i_mi_time[0] != -1.0: mit[0] = round(i_mi_time[0], 3)
      if i_mi_time[1] != -1.0: mit[1] = round(i_mi_time[1], 3)
      if i_mx_time[0] != -1.0: mxt[0] = round(i_mx_time[0], 3)
      if i_mx_time[1] != -1.0: mxt[1] = round(i_mx_time[1], 3)

      new_row = {
        "File": f'Formulas(sat/unsat): {i_formulas[0]}/{i_formulas[1]}',
        "Line": f'Average(sat/unsat): {i_sat_ave}/{i_unsat_ave}',
        "Column": f'Min_time(sat/unsat): {mit[0]}/{mit[1]}',
        "Property": f'Max_time(sat/unsat): {mxt[0]}/{mxt[1]}',
        "Result": '',
        "Time": '',
      }
      w.writerow(new_row)

    new_row = {
        "File": '',
        "Line": '',
        "Column": '',
        "Property": '',
        "Result": '',
        "Time": '',   
    }
    w.writerow(new_row)
    
    sat_ave = round(total_time[0] / formulas[0], 3)
    unsat_ave = round(total_time[1] / formulas[1], 3)

    mit = ['-', '-']
    mxt = ['-', '-']

    if mi_time[0] != -1.0: mit[0] = round(mi_time[0], 3)
    if mi_time[1] != -1.0: mit[1] = round(mi_time[1], 3)
    if mx_time[0] != -1.0: mxt[0] = round(mx_time[0], 3)
    if mx_time[1] != -1.0: mxt[1] = round(mx_time[1], 3)
    new_row = {
        "File": f'Formulas(sat/unsat): {formulas[0]}/{formulas[1]}',
        "Line": f'Average(sat/unsat): {sat_ave}/{unsat_ave}',
        "Column": f'Min_time(sat/unsat): {mit[0]}/{mit[1]}',
        "Property": f'Max_time(sat/unsat): {mxt[0]}/{mxt[1]}',
        "Result": '',
        "Time": '',
    }
    w.writerow(new_row)

def run_expriment_on(benchmark_root, extra_args):
  assert(os.path.exists(benchmark_root))
  
  cprogs = []
  for file in os.listdir(f"{benchmark_root}"):
    if file.endswith(".c"):
      cprogs.append(file)
  
  cprogs = sorted(cprogs)
  
  results = {}
  for cprog in cprogs:
    cprog_path = os.path.join(benchmark_root, cprog)
    results[cprog] = run_on(cprog_path, extra_args)
    collect_results(cprog)

  generate_csv(results)    

if __name__ == '__main__':
  if not os.path.exists(output_root):
    os.mkdir(output_root)
  if not os.path.exists(log_root):
    os.mkdir(log_root)
  if not os.path.exists(vcc_log):  
    os.mkdir(vcc_root)
  
  if "--esbmc" in sys.argv:
    csv_file = os.path.join(output_root, "results_esbmc.csv")

  if sys.argv[1] == "--compile":
    compile()
  elif sys.argv[1] == "--run":
    run_on(sys.argv[2], sys.argv[3:])
  elif sys.argv[1] == "--experiment":
    run_expriment_on(sys.argv[2], sys.argv[3:])
  elif sys.argv[1] == "--help":
    help()
  else:
    assert(False)