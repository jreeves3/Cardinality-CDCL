#!/usr/bin/python

# Utility routines for extractors

import sys

verbLevel = 1
errfile = sys.stdout
careful = False


def setVerbLevel(level):
    global verbLevel
    verbLevel = level

def ewrite(s, level):
    if level <= verbLevel:
        errfile.write(s)
        
def eprint(s, level):
    ewrite(s+'\n', level)

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

class CnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "CNF Exception: " + str(self.value)

# Read CNF file.
# Save list of clauses, each is a list of literals (zero at end removed)
class CnfReader():
    file = None
    clauses = []
    nvar = 0
    
    def __init__(self, fname = None):
        if fname is None:
            opened = False
            self.file = sys.stdin
        else:
            opened = True
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise CnfException("Could not open file '%s'\n" % fname)
        self.nvar = 0
        self.clauses = []
        try:
            self.readCnf()
        except Exception as ex:
            if opened:
                self.file.close()
            raise ex
        
    def readCnf(self):
        lineNumber = 0
        nclause = 0
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            fields = line.split()
            if len(fields) == 0:
                continue
            elif line[0] == 'c':
                continue
            elif line[0] == 'p':
                fields = line[1:].split()
                if len(fields) != 3 or fields[0] != 'cnf':
                    raise CnfException("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    raise CnfException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
            else:
                if nclause == 0:
                    raise CnfException("Line %d.  No header line.  Not cnf" % (lineNumber))
                # Check formatting
                try:
                    lits = [int(s) for s in line.split()]
                except:
                    raise CnfException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if careful and lits[-1] != 0:
                    raise CnfException("Line %d.  Clause line should end with 0" % lineNumber)
                lits = lits[:-1]
                if careful:
                    # Sort literals by variable
                    lits.sort(key = lambda l: abs(l))
                    vars = [abs(l) for l in lits]
                    if len(vars) == 0:
                        raise CnfException("Line %d.  Empty clause" % lineNumber)                    
                    if vars[-1] > self.nvar or vars[0] == 0:
                        raise CnfException("Line %d.  Out-of-range literal" % lineNumber)
                    for i in range(len(vars) - 1):
                        if vars[i] == vars[i+1]:
                            raise CnfException("Line %d.  Opposite or repeated literal" % lineNumber)
                self.clauses.append(lits)
                clauseCount += 1
        if clauseCount != nclause:
            raise CnfException("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))
        return

# Code for generating CNF, order, and schedule files
class WriterException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Writer Exception: " + str(self.value)


# Generic writer
class Writer:
    outfile = None
    opened = False
    suffix = None
    variableCount = 0

    def __init__(self, fname):
        self.variableCount = 0
        if fname is None:
            self.outfile = sys.stdout
            self.opened = False
        else:
            try:
                self.outfile = open(fname, 'w')
            except:
                raise WriterException("Couldn't open file '%s'" % fname)

    def newVariable(self):
        self.variableCount += 1
        return self.variableCount

    def newVariables(self, n):
        return [self.newVariable() for i in range(n)]

    def vcount(self):
        return self.CvariableCount

    def trim(self, line):
        while len(line) > 0 and line[-1] == '\n':
            line = line[:-1]
        return line

    def show(self, line):
        line = self.trim(line)
        ewrite(line+'\n', 3)
        if self.outfile is not None:
            self.outfile.write(line + '\n')

    def finish(self):
        if self.outfile is None:
            return
        self.outfile.close()
        self.outfile = None

                
# Creating KNF (or CNF)
class KnfWriter(Writer):
    constraintCount = 0
    headerComments = []
    outputList = []
    cnfOnly = True

    def __init__(self, fname, variableCount):
        Writer.__init__(self, fname)
        self.variableCount = variableCount
        self.constraintCount = 0
        self.headerComments = []
        self.outputList = []
        self.cnfOnly = True

    # With KNF, must accumulate all of the clauses, since the file header
    # requires providing the number of clauses.

    def doComment(self, line):
        if verbLevel >= 2:
            self.outputList.append("c " + line)

    def doHeaderComment(self, line):
        self.headerComments.append("c " + line)

    def doClause(self, lits):
        for lit in lits:
            var = abs(lit)
            self.variableCount = max(var, self.variableCount)
        sfields = [str(lit) for lit in lits] + ['0']
        self.outputList.append(" ".join(sfields))
        self.constraintCount += 1
        return self.constraintCount

    def doCard(self, const, lits):
        for lit in lits:
            var = abs(lit)
            self.variableCount = max(var, self.variableCount)
        sfields = []
        if const != 1:
            self.cnfOnly = False
            sfields = ['k', str(const)]
        sfields += [str(lit) for lit in lits] + ['0']
        self.outputList.append(" ".join(sfields))
        self.constraintCount += 1
        return self.constraintCount

    def doAlo(self, vars, comment = True):
        if comment:
            svars = [str(v) for v in vars]
            self.doComment("At-Least-One constraint over variables %s" % ", ".join(svars))
        self.doCard(1, vars)

    def doAmo(self, vars, comment = True):
        lits = [-v for v in vars]
        if comment:
            svars = [str(v) for v in vars]
            self.doComment("At-Most-One constraint over variables %s" % ", ".join(svars))
        self.doCard(len(vars)-1, lits)

    def doExactlyOne(self, vars, comment = True):
        if comment:
            svars = [str(v) for v in vars]
            self.doComment("Exactly-One constraint over variables %s" % ", ".join(svars))            
        self.doAlo(vars, comment = False)
        self.doAmo(vars, comment = False)

    def doAtMostK(self, const, vars, comment = True):
        if comment:
            svars = [str(v) for v in vars]
            self.doComment("At-most-%d constraint over variables %s" % (const, ", ".join(svars)))
        lits = [-v for v in vars]
        k = len(vars) - const
        self.doCard(k, lits)

    def finish(self, statOnly = False):
        if self.outfile is None:
            return
        for line in self.headerComments:
            self.show(line)
        tname = "cnf" if self.cnfOnly else "knf"
        self.show("p %s %d %d" % (tname, self.variableCount, self.constraintCount))
        if not statOnly:
            for line in self.outputList:
                self.show(line)
        self.outfile.close()
        self.outfile = None
