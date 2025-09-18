import sys
import getopt
from pysat.card import *

'''
This script parses a KNF formula then encodes to CNF. 

AMO constraints are always encoded using the sequential counter encoding.

Default Execution:

  > python3 order_and_encode.py -k <KNF input> -c <CNF output> -e <encoding type [seqcounter, totalizer, sortnetwrk, cardnetwrk, mtotalizer, kmtotalizer]>

Note on modules,

  pysat module is included for encoding APIs

'''

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

def write_clause(file, clause):
   file.write(' '.join(str (lit) for lit in (clause + [0])) + "\n")

# 1. Parse the KNF formula
def parse_knf (knf_input):
  knf_lines = open(knf_input, 'r')
  
  klauses = []

  for line in knf_lines:
    line = trim(line)
    tokens = line.split()

    if len(tokens) == 0: # empty line
       continue

    if tokens[0] == "p": # p knf header
      continue
  
    if tokens[0] == "c": # comment
       continue
    
    if tokens[0] == "k": # cardinality constraint
      literals = [int(lit) for lit in tokens[2:-1]]
      bound = int (tokens[1])

      klauses.append ((bound, literals))

    else: # standard clause
      literals = [int (lit) for lit in tokens[:-1]] # remove last '0'
      klauses.append((1,literals))

  return klauses

# 4. Encode KNF to CNF using specified encoding type
def write_cnf (klauses, max_var, cnf_output, encoding_type):
  clauses = []
  # loop over input KNF formula, replacing cardinality constraints with encoded clauses
  for (bound, literals) in klauses:
    if bound > 1: # cardinality constraint
      # encode using the specific encoding type from PySAT
      new_cnf = None

      if bound == len(literals) -1: # at most one use seqcounter
          new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.seqcounter) 
      elif encoding_type == "seqcounter":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.seqcounter) 
      elif encoding_type == "totalizer":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.totalizer)
      elif encoding_type == "sortnetwrk":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.sortnetwrk)
      elif encoding_type == "cardnetwrk":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.cardnetwrk)
      elif encoding_type == "mtotalizer":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.mtotalizer)
      elif encoding_type == "kmtotalizer":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.kmtotalizer)
      elif encoding_type == "bitwise":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.bitwise)
      elif encoding_type == "ladder":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.ladder)
      elif encoding_type == "pairwise":
        new_cnf = CardEnc.atleast(literals, bound, max_var,encoding=EncType.pairwise)
      else:
        print(f"Error: encoding type {encoding_type} not recognized")
        exit()

      # Update max variable based on largest auxiliary variable used in the encoding
      max_var = max([max([abs(l) for l in lits]) for lits in new_cnf.clauses])
      clauses = clauses + new_cnf.clauses

    else: # standard clause
      clauses.append(literals)

  # write the output CNF formula
  out_file = open(cnf_output, 'w')

  # header  
  out_file.write("p cnf "+str(max_var)+" "+str(len(clauses))+"\n")

  for clause in clauses:
     write_clause (out_file, clause)

  out_file.close()


def generate_cnf (knf_input, cnf_output, encoding_type):

  max_var = None  # max variables used to set new auxiliary variables in encodings

  # open knf formula
  knf_lines = open(knf_input, 'r')

  # get number of variables from header for 
  for line in knf_lines:
    line = trim(line)
    tokens = line.split()
    if tokens[0] == "p": # pcnf header
      max_var = int(tokens[2])
      # max_cls = int(tokens[3])
      break
  knf_lines.close()

  # parse the KNF
  input_klauses = parse_knf (knf_input)

  write_cnf (input_klauses, max_var, cnf_output, encoding_type)
  
    
def run(name, args):
    
    knf_input = None
    cnf_output = None
    encoding_type = None

    optlist, args = getopt.getopt(args, "hk:c:e:")
    for (opt, val) in optlist:
        if opt == '-k':
            knf_input = val
        elif opt == '-c':
            cnf_output = val
        elif opt == '-e':
          encoding_type = val
        elif opt == '-h':
            print("Usage: "+name+" -k <KNF input> -c <CNF output> -e <encoding type [seqcounter, totalizer, sortnetwrk, cardnetwrk, mtotalizer, kmtotalizer]>")
            exit()
       
    if encoding_type not in ["seqcounter", "totalizer", "sortnetwrk", "cardnetwrk", "mtotalizer", "kmtotalizer"]:
      print(f"Error: encoding type {encoding_type} not recognized")
      exit()

    generate_cnf (knf_input, cnf_output, encoding_type)
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
