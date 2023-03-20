
import sys
import getopt
import random

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s
    
def remove_comment(s):
  for i in range(len(s)):
    if s[i] == 'c': return s[:i]
  return s
  
def permuteStuff(cnfName,outFile,seed,header):
  
  random.seed(seed)
  clauses = []
  nCls = None
  nVar = None
  
  outCnf = open(outFile, 'w')
  
  cnf = open(cnfName, 'r')
  
  #get nvar
  nVar = 0
  knf = False
  for line in cnf:
    line = trim(line)
    tokens = line.split()
    if tokens[0] == "p": # Header
      if tokens[1] == "knf" : knf = True
      nVar = int(tokens[2])
      nCls = int(tokens[3])
      break

  if header :
    if knf: outCnf.write("p knf {} {}\n".format(nVar,nCls))
    else: outCnf.write("p cnf {} {}\n".format(nVar,nCls))
  
  for line in cnf:
    line = trim(line)
    tokens = line.split()
    if tokens[0] == "p": # Header
      continue
    line = remove_comment(line)
    if line == "" : continue
    clauses.append(line)
    
  random.shuffle(clauses)
  for st in clauses:
    outCnf.write(st+"\n")
  outCnf.close()
  cnf.close()
    
def run(name, args):
    cnfName = None
    outFile = None
    seed = 0
    header = True
    
    
    optlist, args = getopt.getopt(args, "hc:s:o:")
    for (opt, val) in optlist:
        if opt == '-c':
            cnfName = val
        elif opt == '-o':
            outFile = val
        elif opt == '-s':
          seed = int(val)
        elif opt == '-h':
          header = True
    
    permuteStuff(cnfName,outFile,seed,header)
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
