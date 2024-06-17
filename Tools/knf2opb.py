
from operator import pos
import sys
import getopt
import random

'''

  Write an opb file in the KNF format

'''



def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s
    
def remove_comment(s):
  for i in range(len(s)):
    if s[i] == 'c': return s[:i]
  return s

def print_gt (lits, bound):
  nFalse = 0
  st = "k"
  for lit in lits:
      if lit < 0: nFalse += 1
  st += " {}".format(bound + nFalse)
  if (bound + nFalse == 1): st = ""
  for lit in lits:
      st += " {}".format(lit)
  st += " 0"
  if (bound + nFalse == 1): st = st[1:]
  return st

def print_lt (lits, bound):
  bound *= -1
  litsP = [lit * -1 for lit in lits]
  return print_gt (litsP, bound)

def print_constraint (bound, lits):
  neg = 0

  st = ""
  for l in lits:
      if l < 0:
        neg += 1
        st += f"-1 x{abs(l)} "
      else:
        st += f"+1 x{abs(l)} "
  st += f">= {bound - neg} ;"
  print (st)

def opb2knf (input_file):
  lines = open (input_file, 'r')

  for line in lines:
    tokens = trim (line).split ()
    if len(tokens) < 1: continue

    bound = 0
    lits = []

    if tokens[0] == "c" : continue 
    if tokens[0] == "p" : 
       nVars = int (tokens[2])
       nCls = int (tokens[3])
       print(f"* #variable= {nVars} #constraint= {nCls}")
       continue

    if tokens[0] == "k" :
       bound = int (tokens[1])
       lits = [int (lit) for lit in tokens[2:-1]]
    else :
       bound = 1
       lits = [int (lit) for lit in tokens[:-1]]

    print_constraint (bound, lits)
    
     

def run(name, args):
    input_file = None
    
    optlist, args = getopt.getopt(args, "f:")
    for (opt, val) in optlist:
        if opt == '-f':
          input_file = val
    
    opb2knf (input_file)
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
