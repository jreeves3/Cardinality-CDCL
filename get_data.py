import sys
import getopt
import functools
import operator
from queue import Queue
import os
from pathlib import Path
import csv
import re
from openpyxl import Workbook
import shutil
import math
  
def tikz_cactus_header(title,xlabel,ylabel):
  return "\\begin{figure}\n% \\centering\n% \\begin{subfigure}[b]{.49\textwidth}\n\\centering\n\\begin{tikzpicture}[scale = 1.05]\n\\begin{axis}[mark options={scale=1.0},grid=both, grid style={black!10},  legend style={at={(0.9,0.2)}}, legend cell align={left},\nx post scale=1,xlabel="+xlabel+", xmode=log,ylabel="+ylabel+",mark size=3pt,    height=12cm,width=12cm,ymin=0,ymax=1000,xmin=0.1,xmax=10000,title={"+title+"}]\n  \n"

def tikz_scatter_header(title,xlabel,ylabel):
  return "\\begin{figure}\n% \\centering\n\\begin{tikzpicture}[scale = 1.05]\n\\begin{axis}[mark options={scale=1.0},grid=both, grid style={black!10},  legend style={at={(0.9,0.2)}}, legend cell align={left},\nx post scale=1,xlabel="+xlabel+", ylabel="+ylabel+",mark size=3pt, xmode=log,    ymode=log,height=12cm,width=12cm,xmin=1,xmax=6000,ymin=1,ymax=6000,title={"+title+"}]\n"
 
def tikz_ender():
  return  "\\end{axis}\n\\end{tikzpicture}\n\\end{figure}"

def tikz_scatter_ender():
  return  "\\addplot[color=black] coordinates {(0.009, 0.009) (5000, 5000)};\n\\addplot[color=black, dashed] coordinates {(0.009, 5000) (5000, 5000)};\n\\addplot[color=black, dashed] coordinates {(5000, 0.009) (5000, 5000)};\n\\legend{SAT, UNSAT}\n\\end{axis}\n\\end{tikzpicture}\n\\end{figure}"

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s
    
def strip_lead(s):
  skip = True
  new_s = ""
  for i in range(len(s)-1,0,-1):
    if skip:
      if s[i] == '.': skip = False
    else:
      if s[i] == '/':
       
        if new_s[-4:] == ".cnf":
          new_s = new_s[:-4]
#          print(new_s)
        return(new_s)
      else: new_s = s[i] + new_s


 
def print_card_extractor_stats (input_card_stats):
  if len(input_card_stats.keys()) != 5353 :
    print("card stats too small!!")
    print(len(input_card_stats.keys()))
  nAny = 0
  nDirectExcl = 0
  nEncodedExcl = 0
  nBoth = 0
  nEncodedK = [0,0,0,0]
  nBelow = 0
  avgRuntime = 0
  avgBelow = 0
  for b in input_card_stats.keys():
    d = input_card_stats[b]
    
    if float(d['\ufeffConRatio']) <= 0.9:
      nBelow += 1
      avgRuntime += float(d['Star_Time_CPU'])
    if int(d['dAmoCnt']) > 0 or int(d['eAmoCnt']) > 0:
      nAny += 1
      if int(d['dAmoCnt']) > 0 and int(d['eAmoCnt']) > 0:
        nBoth += 1
      elif int(d['eAmoCnt']) > 0:
        nEncodedExcl += 1
      else:
        nDirectExcl += 1
    if int(d['eAmoCnt']) > 0:
      kRatio = int(d['EncodeWeightSumK']) / float(d['ElimVars'])
      if kRatio < 1.5: nEncodedK[0] += 1
      elif kRatio < 2.5: nEncodedK[1] += 1
      elif kRatio < 3.5: nEncodedK[2] += 1
      elif kRatio < 4.5: nEncodedK[3] += 1
      else : # extra large ratio
        nEncodedK[3] += 1
  print("Found, Pairwise, Auxiliary, Both, Below 0.9, Avg (s)")
  print((nAny,nDirectExcl,nEncodedExcl,nBoth,nBelow,avgRuntime/nBelow))
  print("table 5, encoded ratios")
  print(nEncodedK)
  
  
def print_solving_stats (input_card_stats,solve_stats,configurations):
  if len(input_card_stats.keys()) != 5353 :
    print("card stats too small!!")
    print(len(input_card_stats.keys()))

  nCon = len(configurations)
  nExclCon = {}
  nSolved = {}
  nSAT = 0
  nUNSAT = 0
  missed = 0
  same = 0
  for c in configurations:
    nExclCon[c] = [0,0]
    nSolved[c] = [0,0]
  cnt = 0
  for b in input_card_stats.keys():
    d = input_card_stats[b]
    if float(d['\ufeffConRatio']) > 0.9:
      continue

    cnt += 1
      
    truth = -1
    for c in configurations:
      result = solve_stats[b]['\ufeffresult']
      if result == "UNSAT":
        truth = 1
      if result == "SAT":
        truth = 0
        
    bestCon = None
    bestConT = 5000
    sameValue = False
    if truth != -1: # someone solved it
      for c in configurations:
        time = float(solve_stats[b][c+'-CPU'])
        if time >= 5000: continue
        if time < bestConT:
          bestConT = time
          bestCon = c
        elif time == bestConT:
          if not sameValue:
            same += 1
          sameValue = True
        nSolved[c][truth] += 1
        
      if bestCon is not None and not sameValue:
        nExclCon[bestCon][truth] += 1
        if truth == 0: nSAT += 1
        else: nUNSAT += 1
      
  
  header = "SAT UNSAT SAT-BEST UNSAT-BEST PERCENT-BEST"
  print(header)
  for c in configurations:
    per = round(100 * (nExclCon[c][0]+nExclCon[c][1]) / float(nSAT + nUNSAT),2)
    st = "{} & {} & {} & {} & {} & {} \\\\".format(c,nSolved[c][0], nSolved[c][1],nExclCon[c][0],nExclCon[c][1],per)
    print(st)
  print(cnt)
  print((nSAT,nUNSAT))

def get_solver_data(file):
  candidates = []
  solve_stats = {}
  # get ratio to determine which benchmarks to use
  with open(file, mode='r') as csvFile:
    csvReader = csv.DictReader(csvFile)
    for line in csvReader:
      temp_b = line["Name"]
      candidates.append(temp_b)
      if not temp_b in solve_stats: solve_stats[temp_b] = {}
      solve_stats[temp_b] = line
  return candidates, solve_stats

def get_squares_data(file):
  candidates = []
  solve_stats = {}
  # get ratio to determine which benchmarks to use
  with open(file, mode='r') as csvFile:
    csvReader = csv.DictReader(csvFile)
    for line in csvReader:
      temp_b = line["\ufeffName"]
      candidates.append(temp_b)
      if not temp_b in solve_stats: solve_stats[temp_b] = {}
      solve_stats[temp_b] = line
  return candidates, solve_stats

def get_extractor_data(file):
  candidates = []
  bench_ratios = {}
  input_card_stats = {}
  # get ratio to determine which benchmarks to use
  with open(file, mode='r') as csvFile:
    csvReader = csv.DictReader(csvFile)
    for line in csvReader:
      temp_b = line["Name"]
      if not temp_b in input_card_stats: input_card_stats[temp_b] = {}
      input_card_stats[temp_b] = line
      con_ratio = float(line["\ufeffConRatio"])
      bench_ratios[temp_b] = con_ratio
      if con_ratio <= 0.90 : # cutoff for experiments
        candidates.append(temp_b)
  return candidates, bench_ratios, input_card_stats
  

  
def print_squares(stat_con, configurations):
## Tikz table formatting

  print("\nMagic Squares")
  configurations = ["ReEncodePair","ReEncode","ccdcl","ccdclPlus"]
  print(list(range(5,13)))
  for c in configurations:
    st = c + " "
    for n in range(5,13):
      b = "magicsq-"+str(n)
      if float(stat_con[b][c+'-CPU']) < 5000:
        st += " & " + str(round(float(stat_con[b][c+'-CPU']) ,2))
      else:
        st += " & -- "
    print(st)

  print("\nMax Squares")
  configurations = ["ReEncode","ccdcl","ccdclPlus"]
  # max squares
  print(str([(7,32),(8,41),(9,51),(10,61),(7,33),(8,42),(9,52),(10,62)]))
  for c in configurations:
    st = c + " "
    for n,m in [(7,32),(8,41),(9,51),(10,61)]:
      b = "maxsquare-"+str(n)+"-"+str(m)+"-SAT"
      if float(stat_con[b][c+'-CPU']) < 5000:
        st += " & " + str(round(float(stat_con[b][c+'-CPU']) ,2))
      else:
        st += " & -- "
    for n,m in [(7,33),(8,42),(9,52),(10,62)]:
      b = "maxsquare-"+str(n)+"-"+str(m)+"-UNSAT"
      if float(stat_con[b][c+'-CPU']) < 5000:
        st += " & " + str(round(float(stat_con[b][c+'-CPU']) ,2))
      else:
        st += " & -- "
    print(st)

def print_scatter(solve_stats,ratios,input_card_stats,config1,config2, benchmarks,config3=None,best=True):
  colors = ["blue","redpurple","midgreen","clearorange","clearyellow","darkestblue", "browngreen","redpurple","black","darkred"]
  marks = ["diamond",""]
  cnt = 0

  data_list = []
  
  for b in benchmarks:
    if ratios[b] > 0.9: continue # only rations below 0.9

    cnt += 1
    
    exMark = False
    truth_value = -1
    result = solve_stats[b]['\ufeffresult']
    if result == "UNSAT":
      truth_value = 1
    if result == "SAT":
      truth_value = 0

    time1 = float(solve_stats[b][config1+'-CPU'])
    time2 = float(solve_stats[b][config2+'-CPU'])
    if config3 is not None:
      if best:
        if float(solve_stats[b][config3+'-CPU']) < time2:
          exMark = True
          time2 = float(solve_stats[b][config3+'-CPU'])
      else:
        if float(solve_stats[b][config3+'-CPU'])> time2:
          exMark = True
          time2 = float(solve_stats[b][config3+'-CPU'])
    
    
    if truth_value == -1: continue # both timeouts
    if time1 < 0.1: time1 = 0.1 # lift to 0.1 so it is shown on the scatter plot
    if time2 < 0.1: time2 = 0.1
    if time1 >= 5000: time1 = 5000 # timeout
    if time2 >= 5000 : time2 = 5000
    if time1 == 5000 and time2 == 5000 : continue # point at top right diagonal
    if time1 == 0.1 and time2 == 0.1 : continue # point at bottom left diagonal
    ratio = 1/math.sqrt(ratios[b]) # size of mark
    ratio = min (ratio,10)
    
    color_mark = truth_value
    if exMark: # change color if coming from additional configuration
      if truth_value == 0:
        color_mark = 2
      else: color_mark = 3
    
    plot = "\\addplot[color="+colors[color_mark]+",mark="+marks[truth_value]+"*,mark size="+str(ratio)+"pt,opacity=0.5] coordinates { "
    plot += "("+str(time1) + "," + str(time2) + ") };"
    
    print(plot)
    
  return cnt


def get_data(plots,tables):

  

  candidates, ratios, input_card_stats = get_extractor_data("data/Anni_2022_Extraction_Final.csv")
  solved_benches,  solve_stats = get_solver_data("data/Anni_2022_Solvers_Final.csv")
  square_benches, square_stats = get_squares_data("data/Squares_Solving_Final.csv")
  
  if tables:
    print("Cardinality Extractor Table\n")
    print_card_extractor_stats (input_card_stats)

    print("\nSat Competition Solving Table\n")
    configurations_check = [ "ReEncode","ccdclMinus","ccdcl","ccdclPlus","cadical"]
    print_solving_stats (input_card_stats,solve_stats,configurations_check)

    print("\nSquares Solving Table\n")
    configurations_check = ["ReEncode","ccdclMinus","ccdcl","ccdclPlus","ReEncodePair"]
    print_squares(square_stats, configurations_check)
    


  if plots:
    
    print("Figure 1\n\n")
    print(tikz_scatter_header("","cadical","ReEncode"))
    print_scatter (solve_stats,ratios,input_card_stats,"cadical","ReEncode",solved_benches)
    print(tikz_scatter_ender())



    print("Figure 2\n\n")
    print(tikz_scatter_header("", "cadical","Best ( ReEncode or ccdcl )"))
    print_scatter (solve_stats,ratios,input_card_stats,"cadical","ccdcl", solved_benches, "ReEncode")
    print(tikz_scatter_ender())

    print("Figure 3\n\n")
    print(tikz_scatter_header("","ccdcl-","ccdcl" ))
    print_scatter (solve_stats,ratios,input_card_stats,"ccdclMinus","ccdcl", solved_benches)
    print(tikz_scatter_ender())

    print("Figure 4\n\n")
    print(tikz_scatter_header("","ccdcl+","Worst ( ReEncode or ccdcl )"))
    print_scatter (solve_stats,ratios,input_card_stats,"ccdclPlus","ccdcl", solved_benches, "ReEncode",False)
    print(tikz_scatter_ender())

  
  
  
 

    
#######################################################################################
# MAIN FUNCTION
#######################################################################################
  
def run(name, args):
    
    plots = False
    tables = False

    optlist, args = getopt.getopt(args, "pt")
    for (opt, val) in optlist:
      if opt == '-p':
          plots = True
      elif opt == '-t':
          tables = True

        
        
    get_data (plots,tables)
        

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
