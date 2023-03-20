
import sys
import getopt

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s
    
def remove_comment(s):
  for i in range(len(s)):
    if s[i] == 'c': return s[:i]
  return s
  
def processAssignment(inFile,outFile,elimFile):

  elimVars = {}
  
  outUnits = open(outFile, 'w')
  inUnits = open(inFile, 'r')
  elimUnits = open(elimFile, 'r')
  
  for line in elimUnits:
    line = trim(line)
    if len(line) > 0: elimVars[int(line)] = 1
        
  for line in inUnits:
    line = trim(line)
    tokens = line.split()
    if len(tokens) < 2: continue
    line = remove_comment(line)
    if int(tokens[0]) in elimVars: continue
    outUnits.write(line+"\n")

  outUnits.close()
  elimUnits.close()
  inUnits.close()
    
def run(name, args):
    inFile = None
    outFile = None
    elimFile = None

    optlist, args = getopt.getopt(args, "e:i:o:")
    for (opt, val) in optlist:
        if opt == '-i':
            inFile = val
        elif opt == '-o':
            outFile = val
        elif opt == '-e':
          elimFile = val

    
    processAssignment(inFile,outFile,elimFile)
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
