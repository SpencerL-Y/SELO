#!/usr/bin/env python3

import os
import sys
import csv
import matplotlib.pyplot as plt

selo_root = "./"
selo_build = os.path.join(selo_root, "build")
selo = os.path.join(selo_build, "src", "esbmc", "esbmc")

output_root = "./output"
log_root = os.path.join(output_root, "Logs")
vcc_root = os.path.join(output_root, "VCCs")
t_log = os.path.join(output_root, "t.log")
vcc_log = os.path.join(output_root, "vcc.log")

csv_file = os.path.join(output_root, "results.csv")
aht_plt_file = os.path.join(output_root, "aht_fig.svg")


def compile():
  os.system(f"cd {selo_build } && cmake --build .")

def help():
  os.system(f"{selo} -h")

  cmds = {
    "--init" : ('', "Init output directory"),
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

def collect_one_assert(info, aht):
  assert(len(info) == 3)
  res = {}
  
  # Location
  res["Line"] = "None"
  res["Column"] = "None"
  if len(info[0].split(' ')) >= 7:
    location = info[0].split(' ')
    res["Line"] = location[4]
    res["Column"] = location[6]



  # Property
  prt = info[2].split(" ")
  res["Property"] = prt[1]

  # Atomic heap term
  res["Aht"] = aht

  # Result & Time
  res["Result"] = prt[3]
  res["Time"] = prt[5].replace('s', '')

  return res

def analysis_result(log):
  assert(os.path.exists(log))

  flag = "--- Result ---"

  assert_results = []
  total_time = 0.0
  is_collecting = False
  with open(log) as log_file:
    info_buf = []
    aht = '-'
    for line in log_file:
      
      if "Number of aht:" in line:
        aht = int(line.strip().split(' ')[3])

      if line.find(flag) != -1:
        if not is_collecting:
          is_collecting = True
          continue
        else:
          is_collecting = False
          one_res = collect_one_assert(info_buf, aht)
          assert_results.append(one_res)
          aht = '-'
          info_buf.clear()
          total_time += float(one_res["Time"])
          
      if not is_collecting: continue
      info_buf.append(line.strip())
  
  return (assert_results, total_time)

def run_on(cprog, extra_args):
  assert(os.path.exists(cprog))
  
  cprog_name = os.path.basename(cprog)
  print(f"Verifying program: {cprog_name}")

  # TODO: add more extra args
  args = [
    selo,
    cprog,
    "--no-library",
    "--force-malloc-success",
    "--memory-leak-check",
    "--result-only",
    "--show-vcc",
    "--output",
    vcc_log,
    "--multi-property",
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
  
  (result, total_time) = analysis_result(t_log)
  for d in result:
    res = [k + ": " + str(v) for k, v in list(d.items())]
    print("{:<10} {:<12} {:<25} {:<10} {:<15} {:<10}".format(*res))

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
    header = ["File", "Line", "Column", "Property", "Aht", "Result", "Time"]
    w = csv.DictWriter(f, header)
    w.writeheader()
    formulas = [0, 0]
    total_time = [0.0, 0.0]
    mi_time = ['-', '-']
    mx_time = ['-', '-']

    theory_solving_formulas = [0, 0]
    theory_solving_total_time = [0.0, 0.0]
    theory_solving_mi_time = ['-', '-']
    theory_solving_mx_time = ['-', '-']
    
    formulas_with_aht = 0
    total_ahts = 0
    mi_aht = '-'
    mx_aht = '-'
    for cprog, assert_results in results.items():
      is_head = True
      i_total_time = 0.0
      for assert_result in assert_results:
        new_row = {'File': cprog if is_head else ''}
        is_head = False
        new_row.update(assert_result)
        w.writerow(new_row)
        
        time = float(assert_result["Time"])
        i_total_time += time
        r = 0 if assert_result["Result"] == "sat" else 1

        formulas[r] += 1
        total_time[r] += time

        time = round(time, 3)
        if mi_time[r] == '-':
          mi_time[r] = time
        else:
          mi_time[r] = min(mi_time[r], time)
        
        if mx_time[r] == '-':
          mx_time[r] = time
        else:
          mx_time[r] = max(mx_time[r], time)

        # Entering theory solving
        if str(assert_result["Aht"]) != '-':
          time = float(assert_result["Time"])

          theory_solving_formulas[r] += 1
          theory_solving_total_time[r] += time
          
          time = round(time, 3)
          if theory_solving_mi_time[r] == '-':
            theory_solving_mi_time[r] = time
          else:
            theory_solving_mi_time[r] = min(theory_solving_mi_time[r], time)
          
          if theory_solving_mx_time[r] == '-':
            theory_solving_mx_time[r] = time
          else:
            theory_solving_mx_time[r] = max(theory_solving_mx_time[r], time)

          # Atomic heap terms statistics
          aht = assert_result["Aht"]
          formulas_with_aht += 1
          total_ahts += aht
          
          if mi_aht == '-': mi_aht = aht
          else: mi_aht = min(mi_aht, aht)

          if mx_aht == '-': mx_aht = aht
          else: mx_aht = max(mx_aht, aht)

      new_row = {
        "File": '',
        "Line": '',
        "Column": '',
        "Property": '',
        "Aht": '',
        "Result": 'Totaltime:',
        "Time": f'{round(i_total_time, 3)}',
      }
      w.writerow(new_row)

    # Solving time statistics
    new_row = {}
    w.writerow(new_row)
    
    # Total time statistics
    sat_ave = round(total_time[0] / formulas[0], 3)
    unsat_ave = round(total_time[1] / formulas[1], 3)

    new_row = {
        "File": f'Formulas(sat/unsat): {formulas[0]}/{formulas[1]}',
        "Line": f'Average(sat/unsat): {sat_ave}/{unsat_ave}',
        "Column": f'Min_time(sat/unsat): {mi_time[0]}/{mi_time[1]}',
        "Property": f'Max_time(sat/unsat): {mx_time[0]}/{mx_time[1]}',
    }
    w.writerow(new_row)

    new_row = {}
    w.writerow(new_row)
    new_row = { 'File' : 'Theory_solving'}
    w.writerow(new_row)

    # Only formulas entering theory solving
    theory_solving_sat_ave = round(theory_solving_total_time[0] / theory_solving_formulas[0], 3)
    theory_solving_unsat_ave = round(theory_solving_total_time[1] / theory_solving_formulas[1], 3)

    new_row = {
        "File": f'Formulas(sat/unsat): {theory_solving_formulas[0]}/{theory_solving_formulas[1]}',
        "Line": f'Average(sat/unsat): {theory_solving_sat_ave}/{theory_solving_unsat_ave}',
        "Column": f'Min_time(sat/unsat): {theory_solving_mi_time[0]}/{theory_solving_mi_time[1]}',
        "Property": f'Max_time(sat/unsat): {theory_solving_mx_time[0]}/{theory_solving_mx_time[1]}',
        "Aht": f'Formulas_with_aht: {formulas_with_aht}',
        "Result": f'Average_aht: {total_ahts // formulas_with_aht}',
        "Time": f'Min/Max(aht): {mi_aht}/{mx_aht}',
      }
    w.writerow(new_row)

def generate_aht_plt(results):
  x = []
  y = []
  for _, assert_results in results.items():
    for assert_result in assert_results:
      if str(assert_result["Aht"]) == '-': continue
      
      x.append(int(assert_result["Aht"]))
      y.append(float(assert_result["Time"]))
  
  plt.scatter(x, y, color="blue")
  xticks = [10, 20, 30, 40, 50, 60]
  plt.xticks(xticks)
  yticks = [5, 10, 15, 20 ,25]
  plt.yticks=(yticks)
  plt.xlabel("number of atomic heap terms")
  plt.ylabel("solving time(s)")
  plt.savefig(aht_plt_file)
  plt.show()

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
  generate_aht_plt(results)


if __name__ == '__main__':
  if "--esbmc" in sys.argv:
    csv_file = os.path.join(output_root, "results_esbmc.csv")

  if sys.argv[1] == "--init":
    if not os.path.exists(output_root):
      os.mkdir(output_root)
    if not os.path.exists(log_root):
      os.mkdir(log_root)
    if not os.path.exists(vcc_log):  
      os.mkdir(vcc_root)
  elif sys.argv[1] == "--compile":
    compile()
  elif sys.argv[1] == "--run":
    run_on(sys.argv[2], sys.argv[3:])
  elif sys.argv[1] == "--experiment":
    run_expriment_on(sys.argv[2], sys.argv[3:])
  elif sys.argv[1] == "--help":
    help()
  else:
    assert(False)