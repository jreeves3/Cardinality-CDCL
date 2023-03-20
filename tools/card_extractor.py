#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2022 Marijn Heule, Randal E. Bryant, Joseph Reeves, Carnegie Mellon University
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################


# Detect encodings of cardinality constraints in CNF file,
# and convert them into KNF representations
# Other clauses pass through unchanged

import getopt
import sys
import glob
import os.path
import time

import exutil
import kanalyze

def usage(name):
    exutil.ewrite("Usage: %s [-S] [-h] [-v VLEVEL] [-t SECS] [-d PATH] [-i IN.cnf] [-o OUT.knf]\n" % name, 0)
    exutil.ewrite("  -h       Print this message\n", 0)
    exutil.ewrite("  -S       Statistics only.  Only generate up to KNF header\n", 0)
    exutil.ewrite("  -v VERB  Set verbosity level (1-4)\n", 0)
    exutil.ewrite("  -t SECS  Limit time spent on each file without reasonable generation rate (default = 300)\n", 0)
    exutil.ewrite("  -T SECS  Limit time spent on each file regardless of generation rate (default = 10000)\n", 0)    
    exutil.ewrite("  -d PATH  Run on all .cnf files in specified directory\n", 0)
    exutil.ewrite("  -i IFILE Input CNF file\n", 0)
    exutil.ewrite("  -o OFILE Output KNF file\n", 0)

# Configuration options

# Attempt to extract constraints other than at-most-one
tryOtherEncoding = False
# What rate of clause deletion is acceptable for long runs?
minDeletionRate = 500.0

# Key/value table where key is tuple
class TupleCache:
    # Mapping from integer hash to (key, value)
    tmap = {}
    hits = 0
    misses = 0

    def __init__(self):
        tmap = {}
        self.hits = 0
        self.misses = 0

    def add(self, key, value):
        idx = hash(key)
        self.tmap[idx] = (key, value)

    def get(self, key):
        idx = hash(key)
        if idx in self.tmap:
            self.hits += 1
            (k,v) = self.tmap[idx]
            if key == k:
                return v
        self.misses += 1
        return None
    
    def showStats(self, level, prefix, kwriter):
        exutil.eprint("%sCache hits = %d, misses = %d" % (prefix, self.hits, self.misses), level)
        kwriter.doHeaderComment("Cache hits: %d" % self.hits)
        kwriter.doHeaderComment("Cache misses: %d" % self.misses) 


# Hold CNF formed from subset of clauses in a larger CNF
# and with variables renumbered so data variables come before encoding variables
class ReducedCnf:
    # Total number of variables
    nvar = None
    ndata = None
    # Reduced set of clauses
    clauses = []
    # Original data variables
    dataVariables = []
    # Original encoding variables
    encodingVariables = []
    success = False
    resourceFailure = False
    functionFailure = False
    functionSuccess = False
    constraints = []

    # Initialized with lists of data & encoding variables + original clauses
    def __init__(self, dvars, evars, oclauses, tcache):
        self.dataVariables = dvars
        self.encodingVariables = evars
        self.ndata = len(dvars)
        self.nvar = self.ndata + len(evars)
        self.resourceFailure = False
        self.functionFailure = False
        vars = dvars + evars
        fmap = { vars[i-1] : i for i in range(1, self.nvar+1) }
        rmap = { i : vars[i-1] for i in range(1, self.nvar+1) }
        self.clauses = []
        for oclause in oclauses:
            clause = self.recodeLiterals(oclause, fmap)
            self.clauses.append(clause)
        tup = self.tuplefy()
        lookup = tcache.get(tup)
        if lookup is None:
            e = kanalyze.Extractor(self, self.ndata)
            self.success = e.success
            self.functionSuccess = e.success
            econstraints = e.constraints
            self.resourceFailure = e.resourceFailure
            self.functionFailure = e.functionFailure
        else:
            self.success, econstraints = lookup
        self.constraints = []
        if self.success:
            for con in econstraints:
                nlits = self.recodeLiterals(con.literals, rmap)
                ncon = kanalyze.Constraint(nlits, con.bound)
                self.constraints.append(ncon)
            if lookup is None:
                tcache.add(tup, (e.success, e.constraints))

    def oldTuplefy(self):
        ls = []
        for clause in self.clauses:
            ls = ls + clause + [0]
        return tuple(ls)

    def tuplefy(self):
        # Figure out total length
        length = 0
        for clause in self.clauses:
            length += len(clause) + 1
        # Allocate
        ls = [0] * length
        # Fill nonzeros
        pos = 0
        for clause in self.clauses:
            for lit in clause:
                ls[pos] = lit
                pos += 1
            pos += 1
        return tuple(ls)
    
    def recodeLiterals(self, lits, map):
        clause = []
        for lit in lits:
            nlit = -map[-lit] if lit < 0 else map[lit]
            clause.append(nlit)
        return clause

class ConstraintFinder:
    # Clauses.  Mapping from ID to clause
    # Removed as they get classified
    clauseDict = {}
    # KNF writer
    kwriter = None

    # List containing sets of literals that form small (3-4 literals) cliques
    # Some of these will be used in encoded AMOs
    smallCliqueLiterals = []
    # Corresponding clauses
    smallCliqueClauseIds = []
    
    # variable IDs of eliminated encoding variables
    encodedVarIDs = []

    # Statistics
    encodingVariableCount = 0
    directAmoCount = 0
    encodedAmoCount = 0
    encodedOtherCount = 0
    directAmoHistogram = {}
    encodedAmoHistogram = {}
    encodedOtherHistogram = {}
    directAmoSeconds = 0.0
    encodedAmoSeconds = 0.0
    encodedOtherSeconds = 0.0
    validationSeconds = 0.0
    directAmoTimeout = False
    encodedAmoTimeout = False
    encodedOtherTimeout = False
    directAmoClauseDeletions = 0
    encodedAmoClauseDeletions = 0
    encodedOtherClauseDeletions = 0
    clauseCount = 0
    failCount = 0
    functionSuccessCount = 0
    functionFailCount = 0
    resourceFailCount = 0
    tcache = None

    def __init__(self, clauseList, kwriter):
        # Create of clause list, but sorting by variable
        self.clauseDict = { idx+1 : clauseList[idx] for idx in range(len(clauseList)) }
        self.kwriter = kwriter
        self.encodedOtherCount = 0
        self.directAmoCount = 0
        self.encodedAmoCount = 0
        self.encodingVariableCount = 0
        self.directAmoHistogram = {}
        self.encodedAmoHistogram = {}
        self.encodedOtherHistogram = {}
        self.encodedAmoSeconds = 0.0
        self.validationSeconds = 0.0
        self.otherValidationSeconds = 0.0
        self.directAmoSeconds = 0.0
        self.clauseCount = 0
        self.failCount = 0
        self.functionSuccessCount = 0
        self.functionFailCount = 0
        self.resourceFailCount = 0
        self.directAmoTimeout = False
        self.encodedAmoTimeout = False
        self.encodedOtherTimeout = False
        self.directAmoClauseDeletions = 0
        self.encodedAmoClauseDeletions = 0
        self.encodedOtherClauseDeletions = 0
        self.tcache = TupleCache()

    # Classify vars regarding how they occur in binary clauses
    # Generate mapping from variable to pair (pos,neg), where each element of the pair is True or False
    def classifyVars(self, maxSize):
        polarityDict = {}
        for clause in self.clauseDict.values():
            if len(clause) > maxSize:
                continue
            for lit in clause:
                var = abs(lit)
                pos,neg = False, False
                if var in polarityDict:
                    pos,neg = polarityDict[var]
                if lit < 0:
                    neg = True
                else:
                    pos = True
                polarityDict[var] = (pos,neg)
        return polarityDict

    # Support routines for finding encoded AMOs

    # Find clauses incident on encoding and data variables
    def buildMaps(self, polarityDict):
        # Build map from each encoding variable to the clauses that contain it
        # Encoding variables occur both positively and negatively
        evarMap = { var : [] for var in polarityDict.keys() if polarityDict[var] == (True,True) }
        # Build map from each program variable to the clauses that contain it
        dvarMap = { var : [] for var in polarityDict.keys() if var not in evarMap }

        for cid in self.clauseDict.keys():
            clause = self.clauseDict[cid]
            assigned = False
            for lit in clause:
                var = abs(lit)
                if var in evarMap:
                    evarMap[var].append(cid)
                elif var in dvarMap:
                    dvarMap[var].append(cid)
        return evarMap, dvarMap

    # Find some encoding variable.  Extract subset of variables and clauses
    # that potentially encode cardinality constraint
    def getCluster(self, evarMap, dvarMap):
        # Sets of variables
        dset = set([])
        eset = set([])
        # Set of clause IDs
        idset = set([])
        # Tainted variables: Potential encoding variables that turn out not to work
        # They taint all encoding variables that occur in same clause
        tset = set([])
        # Grab an encoding variable as starting point
        ev = next(iter(evarMap))
        traceSet = set([ev])
        eset.add(ev)
        # Follow transitive closure from pairs of encoding variables
        ok = True
        while len(traceSet) > 0:
            ev = traceSet.pop()
            for cid in evarMap[ev]:
                idset.add(cid)
                clause = self.clauseDict[cid]
                for lit in clause:
                    var = abs(lit)
                    if var == ev or var in eset or var in dset:
                        continue
                    if var in evarMap:
                        traceSet.add(var)
                        eset.add(var)
                    elif var in dvarMap:
                        dset.add(var)
                    else:
                        # Oops.  Potential encoding variable not fully contained in cluster
                        ok = False
                        if var in evarMap:
                            tset.add(var)
            del evarMap[ev]
        # Process consequences of tainting
        while len(tset) > 0:
            ev = tset.pop()
            for cid in evarMap[ev]:
                for lit in clause:
                    var = abs(lit)
                    if var == ev:
                        continue
                    if var in evarMap:
                        tset.add(var)
            del evarMap[ev]
        return ok, dset, eset, idset

    # Add additional binary clauses that contain only variables in cluster
    def expandCluster(self, dvarMap, dset, eset, idset):
        for dv in dset:
            for cid in dvarMap[dv]:
                if cid not in self.clauseDict:
                    continue
                clause = self.clauseDict[cid]
                if len(clause) > 2:
                    continue
                inCluster = True
                for lit in clause:
                    var = abs(lit)
                    if var not in dset and var not in eset:
                        inCluster = False
                if inCluster:
                    idset.add(cid)


    # Order variables according to how they first occur in clauses
    def normalizeCluster(self, dset, eset, idset):
        clauseIds = sorted(idset)
        dvars = []
        evars = []
        for cid in clauseIds:
            clause = self.clauseDict[cid]
            for lit in clause:
                var = abs(lit)
                if var in dset:
                    dvars.append(var)
                    dset.remove(var)
                elif var in eset:
                    evars.append(var)
                    eset.remove(var)
        return dvars, evars, clauseIds

    def findEncodedAmos(self, minSeconds, maxSeconds):
        startTime = time.time()
        polarityDict = self.classifyVars(2)
        self.findEncodedConstraints(minSeconds, maxSeconds, polarityDict, amo=True)
        self.encodedAmoSeconds += time.time() - startTime

    def findEncodedOthers(self, minSeconds, maxSeconds):
        startTime = time.time()
        polarityDict = self.classifyVars(3)
        self.findEncodedConstraints(minSeconds, maxSeconds, polarityDict, amo=False)
        self.encodedOtherSeconds += time.time() - startTime

    def findEncodedConstraints(self, minSeconds, maxSeconds, polarityDict, amo=False):
        startTime = time.time()
        evarMap, dvarMap = self.buildMaps(polarityDict)
        # Build up clusters, each containing set of encoding and program variables
        # Do so by following chains of encoding variables
        while len(evarMap) > 0:
            # See if have hit time bound
            elapsed = time.time() - startTime
            if elapsed > minSeconds:
                deletions = self.encodedAmoClauseDeletions if amo else self.encodedOtherClauseDeletions
                rate = deletions / elapsed
                if rate < minDeletionRate or maxSeconds is not None and elapsed > maxSeconds:
                    exutil.eprint("Timing out.  Elapsed = %.2f secs, minSeconds = %d, maxSeconds = %s.  Deletion Rate = %.2f" % (elapsed, minSeconds, str(maxSeconds), rate), 2)
                    if amo:
                        self.encodedAmoTimeout = True
                    else:
                        self.encodedOtherTimeout = True
                    break
            ok, dset, eset, idset = self.getCluster(evarMap, dvarMap)

            if not ok or len(dset) < 3:
                # Not interesting
                continue

            if len(dset) > 1000:
                # Not going to happen!
                continue

            if len(eset) > 2000:
                continue

            if amo and len(eset) > 3 * len(dset):
                # Too many encoding variables for an AMO
                continue
            
            if not amo and 2 * len(eset) > len(dset) * len(dset):
                # Too many encoding variables for any cardinality constraint
                continue

            if len(dset) > 10 and 3 * len(eset) < len(dset):
                # Not enough encoding variables for an AMO
                continue
            
            self.expandCluster(dvarMap, dset, eset, idset)

            dvars, evars, clauseIds = self.normalizeCluster(dset, eset, idset)

            # Make sure this is really a constraint, and adjust parameters
            self.validateConstraint(dvars, evars, clauseIds)


    # See if this set of clauses really encodes a cardinality constraint
    # If so, turn into KNF.  Otherwise, leave clauses intact
    def validateConstraint(self, dvars, evars, clauseIds):
        startTime = time.time()
        rclauses = [self.clauseDict[cid] for cid in clauseIds]
        exutil.eprint("Attempt to extract cardinality constraint over %d data variables %d encoding variables " % (len(dvars), len(evars)), 3)
        rcnf = ReducedCnf(dvars, evars, rclauses, self.tcache)
        if rcnf.success:
            self.encodingVariableCount += len(evars)
            self.encodedVarIDs += evars
            self.kwriter.doComment("Cardinality constraint over variables %s" % str(dvars))
            self.kwriter.doComment("Replace clauses %s" % str(clauseIds))
            self.kwriter.doComment("Eliminate encoding variables %s" % str(evars))
            deletionCount = 0
            for cid in clauseIds:
                del self.clauseDict[cid]
                deletionCount += 1
            amoCount = 0
            otherCount = 0
            for con in rcnf.constraints:
                bound = con.bound
                card = len(con.literals)
                if bound == 1:
                    self.clauseCount += 1
                    deletionCount -= 1
                elif bound == card-1:
                    if card in self.encodedAmoHistogram:
                        self.encodedAmoHistogram[card] += 1
                    else:
                        self.encodedAmoHistogram[card] = 1
                    self.encodedAmoCount += 1
                    amoCount += 1
                else:
                    self.encodedOtherCount += 1
                    if (card,bound) in self.encodedOtherHistogram:
                        self.encodedOtherHistogram[(card, bound)] += 1
                    else:
                        self.encodedOtherHistogram[(card, bound)] = 1
                    self.kwriter.doComment("NOTE: Nonstandard constraint %d/%d" % (bound, card))
                    otherCount += 1
                self.kwriter.doCard(bound, con.literals)
            if deletionCount > 0 and amoCount + otherCount > 0:
                self.encodedAmoClauseDeletions += deletionCount * amoCount / (amoCount + otherCount)
                self.encodedOtherClauseDeletions += deletionCount * otherCount / (amoCount + otherCount)
            if rcnf.functionSuccess:
                self.functionSuccessCount += 1
        else:
            self.failCount += 1
            if rcnf.functionFailure:
                self.functionFailCount += 1
            if rcnf.resourceFailure:
                self.resourceFailCount += 1
        self.validationSeconds += time.time() - startTime

    # Support routines for direct AMO detection
    def emitAmo(self, literals, clauses):
        self.kwriter.doComment("Generating AMO constraint over literals %s" % str(literals))
        clauses.sort()
        self.kwriter.doComment("Replace clauses %s" % str(clauses))
        self.kwriter.doAmo(literals, comment = False)
        for cid in clauses:
            self.directAmoClauseDeletions += 1
            del self.clauseDict[cid]
        card = len(literals)
        if card in self.directAmoHistogram:
            self.directAmoHistogram[card] += 1
        else:
            self.directAmoHistogram[card] = 1
        self.directAmoCount += 1

    def buildPairGraph(self):
        # Mapping from literal to set of adjacent literals
        # Map in both directions
        edgeMap = {}
        # Mapping from sorted var tuples to clause id
        idMap = {}
        idList = sorted(self.clauseDict.keys())
        # Build graph
        for cid in idList:
            clause = self.clauseDict[cid]
            if len(clause) != 2:
                continue
            # Clauses contain negations of constraint literals
            l1, l2 = -clause[0], -clause[1]
            # Order by absolute value
            if abs(l1) > abs(l2):
                l1, l2 = l2, l1
            idMap[(l1,l2)] = cid
            if l1 not in edgeMap:
                edgeMap[l1] = set([])
            edgeMap[l1].add(l2)
            if l2 not in edgeMap:
                edgeMap[l2] = set([])
            edgeMap[l2].add(l1)
        return edgeMap, idMap

    def expandClique(self, lit, edgeMap):
        cliqueSet = set([lit])
        for olit in edgeMap[lit]:
            include = True
            for clit in cliqueSet:
                if olit != clit and clit not in edgeMap[olit]:
                    include = False
                    break
            if include:
                cliqueSet.add(olit)
        return cliqueSet

    def removeEdge(self, l1, l2, edgeMap, idMap):
        pair = (l1,l2)
        del idMap[pair]
        edgeMap[l1].remove(l2)
        edgeMap[l2].remove(l1)
        

    def findCliqueClauses(self, litList, edgeMap, idMap):
        clauseList = []
        for i1 in range(len(litList)):
            l1 = litList[i1]
            for i2 in range(i1+1, len(litList)):
                l2 = litList[i2]
                cid = idMap[(l1,l2)]
                clauseList.append(cid)
                self.removeEdge(l1, l2, edgeMap, idMap)
        return clauseList

    def findDirectAmos(self, minSeconds, maxSeconds):
        self.smallCliqueLiterals = []
        self.smallCliqueClauseIds = []
        startTime = time.time()
        edgeMap, idMap = self.buildPairGraph()

        while len(idMap) > 0:

            # See if have hit time bound
            elapsed = time.time() - startTime
            if elapsed > minSeconds:
                rate = self.directAmoClauseDeletions / elapsed
                if rate < minDeletionRate or maxSeconds is not None and elapsed > maxSeconds:
                    exutil.eprint("Timing out.  Elapsed = %.2f secs, minSeconds = %d, maxSeconds = %s.  Deletion Rate = %.2f" % (elapsed, minSeconds, str(maxSeconds), rate), 2)
                    self.directAmoTimeout = True
                    break
            # Identify set of literals forming a clique
            # Grab an edge
            for l1,l2 in idMap.keys():
                break
            # Expand into clique
            cliqueSet = self.expandClique(l1, edgeMap)
            # Now have clique literals.  Put this together
            literals = sorted([lit for lit in cliqueSet], key=lambda lit: abs(lit))
            if len(literals) < 3:
                # Not interesting
                l1, l2 = literals
                self.removeEdge(l1, l2, edgeMap, idMap)
                continue
            clauseList = self.findCliqueClauses(literals, edgeMap, idMap)
            if len(literals) <= 4:
                # This might be useful, but it might also be part of an encoded AMO
                self.smallCliqueLiterals.append(literals)
                self.smallCliqueClauseIds.append(clauseList)
            else:
                self.emitAmo(literals, clauseList)
        self.directAmoSeconds += time.time() - startTime

    def finishSmallAmo(self):
        startTime = time.time()
        for litList,clauseList in zip(self.smallCliqueLiterals, self.smallCliqueClauseIds):
            present = True
            for cid in clauseList:
                if cid not in self.clauseDict:
                    present = False
                    break
            if present:
                self.emitAmo(litList, clauseList)
        self.directAmoSeconds += time.time() - startTime

    def generate(self, prefix, minSeconds, maxSeconds, startTime):
        self.findDirectAmos(minSeconds, maxSeconds)
        self.findEncodedAmos(minSeconds, maxSeconds)
        self.finishSmallAmo()
        if tryOtherEncoding:
            self.findEncodedOthers(minSeconds, maxSeconds)

        clauseList = sorted(self.clauseDict.keys())
        if len(clauseList) > 0:
            self.kwriter.doComment("Ordinary clauses")
        for cid in clauseList:
            self.kwriter.doClause(self.clauseDict[cid])
            self.clauseCount += 1
        endTime = time.time()
        elapsed = endTime-startTime
        amoCount = self.directAmoCount + self.encodedAmoCount
        suffix = " (timed out)" if self.encodedAmoTimeout or self.directAmoTimeout else ""
        exutil.ewrite("%sFound %d clausal constraints, %d AMO constraints, %d other constraints (%d failures) %.2f secs%s\n" % 
                      (prefix, self.clauseCount, amoCount, self.encodedOtherCount, self.failCount, elapsed, suffix), 1)
        self.kwriter.doHeaderComment("Clausal constraints: %d" % self.clauseCount)
        self.kwriter.doHeaderComment("Direct AMO constraints: %d" % self.directAmoCount)
        if self.directAmoCount > 0:
            cardList = [("%d:%d" % (card , self.directAmoHistogram[card])) for card in sorted(self.directAmoHistogram.keys())]
            self.kwriter.doHeaderComment("Direct AMO sizes: %s" % " ".join(cardList))
        self.kwriter.doHeaderComment("Encoded AMO constraints: %d" % self.encodedAmoCount)
        self.kwriter.doHeaderComment("Encoding variables eliminated: %d" % self.encodingVariableCount)
        if self.encodingVariableCount > 0:
            varList = [str(var) for var in sorted(self.encodedVarIDs)]
            self.kwriter.doHeaderComment("Eliminated variables IDs: %s" % " ".join(varList))
        if self.encodedAmoCount > 0:
            cardList = [("%d:%d" % (card , self.encodedAmoHistogram[card])) for card in sorted(self.encodedAmoHistogram.keys())]
            self.kwriter.doHeaderComment("Encoded AMO sizes: %s" % " ".join(cardList))
        self.kwriter.doHeaderComment("Other constraints: %d" % self.encodedOtherCount)
        if self.encodedOtherCount > 0:
            cardList = [("%d/%d:%d" % (bound, card, self.encodedOtherHistogram[(card,bound)])) for (card,bound) in sorted(self.encodedOtherHistogram.keys())]
            self.kwriter.doHeaderComment("Other constraint sizes: %s" % " ".join(cardList))
        self.kwriter.doHeaderComment("Failed cardinality justifications: %d" % self.failCount)
        tryCount = self.functionSuccessCount + self.functionFailCount + self.resourceFailCount
        self.kwriter.doHeaderComment("Attempted extractions: %d" % tryCount)        
        self.kwriter.doHeaderComment("  Extraction successes: %d" % self.functionSuccessCount)
        self.kwriter.doHeaderComment("  Extraction function failures: %d" % self.functionFailCount)
        self.kwriter.doHeaderComment("  Extraction resource failures: %d" % self.resourceFailCount)
        self.tcache.showStats(2, prefix, self.kwriter)
        self.kwriter.doHeaderComment("Elapsed seconds: %.2f" % elapsed)
        self.kwriter.doHeaderComment("Direct AMO seconds: %.2f" % self.directAmoSeconds)
        self.kwriter.doHeaderComment("  Direct AMO timed out: %s" % str(self.directAmoTimeout)) 
        self.kwriter.doHeaderComment("Encoded AMO seconds: %.2f" % self.encodedAmoSeconds)
        self.kwriter.doHeaderComment("  Encoded AMO timed out: %s" % str(self.encodedAmoTimeout)) 
        if self.encodedOtherCount > 0:
            self.kwriter.doHeaderComment("Other constraint seconds: %.2f" % self.encodedOtherSeconds)
            self.kwriter.doHeaderComment("  Other constraint timed out: %s" % str(self.encodedOtherTimeout)) 
        self.kwriter.doHeaderComment("Validation seconds: %.2f" % self.validationSeconds)
        return True

def getFile(path):
    fields = path.split("/")
    return fields[-1]

def getRoot(fname):
    fields = fname.split(".")
    if len(fields) > 1:
        fields = fields[:-1]
    return ".".join(fields)

def processFile(iname, oname, minSeconds, maxSeconds, statOnly):
    startTime = time.time()
    prefix = "File %s" % iname
    try:
        creader = exutil.CnfReader(iname)
    except Exception as ex:
        exutil.eprint("%s Failed to read CNF file (%s)" % (prefix, str(ex)), 0)
        return False
    prefix = "File %s (%d vars, %d clauses):" % (iname, creader.nvar, len(creader.clauses))
    try:
        kwriter = exutil.KnfWriter(oname, creader.nvar)
        kwriter.doHeaderComment("Input file: %s" % iname)
        kwriter.doHeaderComment("Input variables: %d" % creader.nvar)
        kwriter.doHeaderComment("Input clauses: %s" % len(creader.clauses))
    except Exception as ex:
        exutil.eprint("%s Failed to set up KNF file (%s)" % (prefix, str(ex)), 0)
        return False
    try:
        cf = ConstraintFinder(creader.clauses, kwriter)
        cf.generate(prefix, minSeconds, maxSeconds, startTime)
        kwriter.finish(statOnly)
    except Exception as ex:
        exutil.eprint("%s Failed to extract constraints (%s)" % (prefix, str(ex)), 0)
        raise ex
        return False
    return True

def run(name, args):
    path = None
    iname = None
    oname = None
    minSeconds = 300
    maxSeconds = 10000
    statOnly = False
    exutil.errfile = sys.stderr
    scount = 0
    fcount = 0
    ecount = 0

    optlist, args = getopt.getopt(args, "hSv:t:T:d:i:o:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-S':
            statOnly = True
        elif opt == '-v':
            exutil.setVerbLevel(int(val))
        elif opt == '-t':
            minSeconds = int(val)
        elif opt == '-T':
            maxSeconds = int(val)
        elif opt == '-i':
            iname = val
        elif opt == '-d':
            path = val
            exutil.errfile = sys.stdout
        elif opt == '-o':
            oname = val
            exutil.errfile = sys.stdout

    if path is not None and iname is not None:
        print("Must specify either path for entire directory or single file, but not both")
        usage(name)
        return

    if path is None:
        processFile(iname, oname, minSeconds, maxSeconds, statOnly)
    else:
        if len(path) > 0 and path[-1] == '/':
            path = path[:-1]
        pnames = sorted(glob.glob(path + "/*.cnf"))
        exutil.eprint("Processing all %d CNF files in directory %s" % (len(pnames), path), 1)
        for pname in pnames:
            iname = getFile(pname)
            root = getRoot(iname)
            oname = root + ".knf"
            if os.path.exists(oname):
                ecount += 1
            elif processFile(iname, oname, minSeconds, maxSeconds, statOnly):
                scount += 1
            else:
                fcount += 1
        exutil.eprint("Extraction results: %d successes, %d failures %d skipped" % (scount, fcount, ecount), 1)
            

if __name__ == "__main__":
    # Increase maximum recursion depth
    sys.setrecursionlimit(10 * sys.getrecursionlimit())
    run(sys.argv[0], sys.argv[1:])

        
            
            
