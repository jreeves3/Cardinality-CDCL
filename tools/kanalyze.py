#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2022 Joseph E. Reeves, Marijn Heule, Randal E. Bryant, Carnegie Mellon University
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


# Given CNF file with the following properties:
#  * Contains only clauses encoding (possible) cardinality constraint
#  * All encoding variables have higher indices problem variables
#
# 1. Detect if it is a cardinality constraint
# 2. Emit KNF declaration(s), giving A) Polarity of problem variables and 2) Constant
#    One declaration if constraint is one-sided, two if it is two-sided

# E.g., given

# p cnf 3 4
# -1 -2 0
# -1 -3 0
# -2 -3 0
# 1 2 3 0

# Will emit:
# k 2 -1 -2 -3 0
# 1 2 3 0

import sys
import getopt
import datetime

import exutil
import bdd
import random


def usage(name):
    print("Usage %s: [-h] [-v VERB] -n N -i INFILE.cnf" % name)
    print("  -h                     Print this message")
    print("  -v VERB                Set verbosity level")
    print("  -n N                   Specify number of problem variables")
    print("  -i INFILE.cnf          Input cardinality CNF file")

seed = 123456
# Parameters for graph diameter seeking
candidateCount = 10

# Parameters to limit runaway BDDs
maxNodeCount = 20000
maxBddSize = 1000

# Representation of intermediate layers of cardinality constraint builder
# Work in constraint-normalized form.
# I.e., view constraint as sum of literals
class CardLayer:
    mgr = None
    # Number layers from 1 to n (the number of variables)
    # Array size = layer+1
    # Entry i designates node reached at this layer when preceding literals sum to i
    nodes = []

    def __init__(self, mgr, nodes):
        self.mgr = mgr
        self.nodes = nodes
        
    def __str__(self):
        slist = [str(node) for node in self.nodes]
        return str(slist)

    # Get children of BDD node.  Error if not leaf or at given level
    def getChild(self, node, vid, phase):
        if node.isLeaf():
            return node
        if node.variable.id == vid:
            return node.high if phase == 1 else node.low
        else:
            raise bdd.BddException("Node %s does not split at id %d" % (str(node), vid))

    # Try to extend to next level with given phase
    def tryExtend(self, phase, vid):
        try:
            incrs = [self.getChild(n, vid, phase) for n in self.nodes]
            sames = [self.getChild(n, vid, 1-phase) for n in self.nodes]
        except bdd.BddException:
            return None
        for ns,ni in zip(sames[1:], incrs[:-1]):
            if ns != ni:
                return None
        return CardLayer(self.mgr, sames[:1] + incrs)
                
    def extend(self, vid):
        cl = None
        phase = 0
        for rp in range(2):
            phase = 1-rp
            cl = self.tryExtend(phase, vid)
            if cl is not None:
                break
        if cl is None:
            return (None, None)
        else:
            return (cl, phase)
        

    # Do a final check, return (lb,ub):
    # Return (lb, ub)
    # Possible Outcomes:
    # (None, None): Cannot be encoded as pair of cardinality constraints
    # (L, H): with 0 <= L <= H <= layer
    # (1, 0):  Unsatisfiable
    def check(self):
        n = len(self.nodes)-1
        L = 0
        U = n
        lvalues = [1 if n == self.mgr.leaf1 else 0 if n == self.mgr.leaf0 else -1 for n in self.nodes]
        if -1 in lvalues:
            return (None, None)
        if 1 not in lvalues:
            # False
            return (1, 0)
        if 0 not in lvalues:
            return (L, U)
        # Look for Lower bound
        for i in range(U):
            if lvalues[i] == 1:
                L = i
                break
        # Look for Upper bound
        for i in range(U, L-1, -1):
            if lvalues[i] == 1:
                U = i
                break
        return (L, U)
        

# Cardinality constraint
class Constraint:
    literals = []
    bound = []

    def __init__(self, lits, b):
        self.literals = sorted(lits, key = lambda lit: abs(lit))
        self.bound = b

    def knfString(self):
        fields = [str(lit) for lit in self.literals] + ["0"]
        if self.bound != 1:
            fields = ["k", str(self.bound)] + fields
        return " ".join(fields)


class PermutationException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Permutation Exception: " + str(self.value)


class Permuter:
    forwardMap = {}
    reverseMap = {}
    
    def __init__(self, valueList = [], permutedList = []):
        self.permutedList = []
        self.forwardMap = {}
        self.reverseMap = {}
        identity = False
        if len(permutedList) == 0:
            permutedList = valueList
            identity = True
        if len(valueList) != len(permutedList):
            raise PermutationException("Unequal list lengths: %d, %d" % (len(valueList), len(permutedList)))
        for v, p in zip(valueList, permutedList):
            self.forwardMap[v] = p
            self.reverseMap[p] = v
        if identity:
            return
        # Check permutation
        for v in valueList:
            if v not in self.reverseMap:
                raise PermutationException("Not permutation: Nothing maps to %s" % str(v))
        for v in permutedList:
            if v not in self.forwardMap:
                raise PermutationException("Not permutation: %s does not map anything" % str(v))
            
    def forward(self, v):
        if v not in self.forwardMap:
            raise PermutationException("Value %s not in permutation" % (str(v)))
        return self.forwardMap[v]

    def reverse(self, v):
        if v not in self.reverseMap:
            raise PermutationException("Value %s not in permutation range" % (str(v)))
        return self.reverseMap[v]
    
    def rpermute(self, ls):
        return sorted(ls, key = lambda x: self.reverse(x))

    def __len__(self):
        return len(self.forwardMap)



# Find a good BDD ordering for variables
# Build undirected graph between encoding variables
# Identify endpoints separated by max diameter
# and order from one end to the other
class ClauseGraph:
    # List of data variables
    dataVariables = []
    # Number of clauses containing each data variable
    dataWeights = {}
    # List of vertices
    encodingVariables = []
    # Adjacency lists
    edgeMap = {}
    # For each data variable, what encoding variables occur in the clauses with it
    dataNeighbors = {}
    # For each encoding variable, what data variables occur in clauses with it
    encodingNeighbors = {}
    # Which encoding clauses are in unit variables
    unitVariables = set([])

    def __init__(self, creader, ndata):
        self.dataVariables = list(range(1, ndata+1))
        self.dataWeights = { v : 0 for v in self.dataVariables }
        self.dataNeighbors = { v : set([]) for v in self.dataVariables }
        self.encodingVariables = list(range(ndata+1, creader.nvar+1))
        self.encodingNeighbors = { v : set([]) for v in self.encodingVariables }
        self.edgeMap = { v : set([]) for v in self.encodingVariables }
        self.unitVariables = set([])
        for clause in creader.clauses:
            vars = [abs(lit) for lit in clause]
            for idx1 in range(len(vars)):
                for idx2 in range(idx1+1, len(vars)):
                    self.addEdge(vars[idx1], vars[idx2])
            if len(vars) == 1 and not self.isData(vars[0]):
                self.unitVariables.add(vars[0])

    def isData(self, v):
        return v <= len(self.dataVariables)

    def addEdge(self, v1, v2):
        if self.isData(v1):
            self.dataWeights[v1] += 1
            if not self.isData(v2):
                self.dataNeighbors[v1].add(v2)
                self.encodingNeighbors[v2].add(v1)
        else:
            if self.isData(v2):
                self.dataWeights[v2] += 1
                self.dataNeighbors[v2].add(v1)
                self.encodingNeighbors[v1].add(v2)
            else:
                self.edgeMap[v1].add(v2)
                self.edgeMap[v2].add(v1)

    # Find nodes furthest from root.  Return (distance, nodeSet)
    def furthestFrom(self, root):
        distance = 0
        horizon = set([root])
        visited = set([])
        while True:
            visited |= horizon
            nhorizon = set([])
            for u in horizon:
                for v in self.edgeMap[u]:
                    if v not in visited:
                        nhorizon.add(v)
            if len(nhorizon) == 0:
                return (distance, horizon)
            else:
                distance += 1
                horizon = nhorizon

    # Assign breadth-first level to every node
    def levelize(self, root):
        n = len(self.encodingVariables)
        dmap = { v : n for v in self.encodingVariables }
        distance = 0
        horizon = set([root])
        visited = set([])
        while True:
            visited |= horizon
            nhorizon = set([])
            for u in horizon:
                dmap[u] = distance
                for v in self.edgeMap[u]:
                    if v not in visited:
                        nhorizon.add(v)
            if len(nhorizon) == 0:
                return dmap
            else:
                distance += 1
                horizon = nhorizon

    def hop(self, vset, count):
        while count > 0:
            count -= 1
            nvset = set([])
            for v in vset:
                distance, horizon = self.furthestFrom(v)
                nvset |= horizon
            vset = nvset
        return vset

    def findCorner(self):
        # If there are unit clauses, then these indicate possible corners
        if len(self.unitVariables) > 0:
            possibleCorners = set(self.unitVariables)
            reach = possibleCorners
        else:
            # Perform hop from a randomly chosen subset of the nodes
            evlist = [v for v in self.encodingVariables if len(self.edgeMap[v]) > 0]
            minWeight = min(self.dataWeights.values())
            dataCorners = [v for v in self.dataVariables if self.dataWeights[v] == minWeight ]
            possibleCorners = set([])
            for v in dataCorners:
                possibleCorners |= self.dataNeighbors[v]
            exutil.eprint("Identify possible corners %s" % str(possibleCorners), 3)
            candidates = random.sample(evlist, candidateCount) if len(evlist) > candidateCount else evlist
            reach = self.hop(candidates, 1)
        # Now choose best of those reached
        bestv = None
        bestDistance = 0
        bestHorizon = set([])
        for v in reach:
            distance, horizon = self.furthestFrom(v)
            if distance > bestDistance or distance == bestDistance and v in possibleCorners:
                bestv = v
                bestDistance = distance
                bestHorizon = horizon
                exutil.eprint("  Max distance from %s is %d with horizon %s" % (str(bestv), bestDistance, str(bestHorizon)), 3)
        niceHorizon = bestHorizon & possibleCorners
        if len(niceHorizon) > 0:
            bestHorizon = niceHorizon
        otherv = random.choice(list(bestHorizon))
        exutil.eprint("Got corner %s.  Diameter = %d.  Horizon = %s.  Using %s" % (str(bestv), bestDistance, str(bestHorizon), otherv), 3)
        return bestv, otherv
        
    def rankEncoding(self):
        source, sink = self.findCorner()
        sourceLevels = self.levelize(source)
        sinkLevels = self.levelize(sink)
        n = len(self.encodingVariables)
        ranks = { v : (n+1) * sourceLevels[v] + n-sinkLevels[v] for v in self.encodingVariables }
        if exutil.verbLevel >= 3:
            exutil.ewrite("Assigned rank values:", 3)
            for v in self.encodingVariables:
                exutil.ewrite(" %d:%d" % (v, ranks[v]), 3)
            exutil.ewrite("\n", 3)
        return sorted(self.encodingVariables, key = lambda v: ranks[v])

    def buildOrder(self):
        if len(self.encodingVariables) == 0:
            return Permuter(self.dataVariables)
        if len(self.encodingVariables) == 1:
            outList = self.encodingVariables + self.dataVariables
        else:
            outList = []
            evars = self.rankEncoding()
            dvars = set(self.dataVariables)
            for e in evars:
                outList.append(e)
                for d in self.encodingNeighbors[e]:
                    self.dataNeighbors[d].remove(e)
                    if len(self.dataNeighbors[d]) == 0:
                        outList.append(d)
                        dvars.remove(d)
            for d in dvars:
                outList.append(d)
        varList = list(range(1, 1+len(outList)))
        exutil.eprint("Ordered variables: %s" % str(outList), 3)
        return Permuter(varList, outList)

class Extractor:
    mgr = None
    creader = None
    ndata = 0
    permuter = None
    buckets = {}
    # Ordered list of encoding levels
    encodingIds = []
    litMap = []
    success = False
    resourceFailure = False
    functionFailure = False
    constraints = []

    def __init__(self, creader, ndata = None):
        self.creader = creader
        if ndata is None:
            self.ndata = self.creader.nvar
        else:
            self.ndata = ndata
        self.success = False
        self.resourceFailure = False
        self.functionFailure = False
        self.constraints = []
        # Order variables
        cg = ClauseGraph(creader, ndata)
        self.permuter = cg.buildOrder()
        self.mgr = bdd.Manager(rootGenerator = self.checkBuckets, verbLevel = exutil.verbLevel)
        self.litMap = {}
        for level in range(1, creader.nvar+1):
            inputId = self.permuter.forward(level)
            var = self.mgr.newVariable(name = "V%d" % inputId, id = inputId)
            t = self.mgr.literal(var, 1)
            e = self.mgr.literal(var, 0)
            self.litMap[ inputId] = t
            self.litMap[-inputId] = e
        self.mgr.setLimit(maxNodeCount)
        root = self.generateBdd()
        if root is None:
            self.resourceFailure = True
        else:
            (phases, lb, ub) = self.findConstraints(root)
            if phases is None:
                self.functionFailure = True
            else:
                self.success = True
                self.constraints = self.getConstraints(phases, lb, ub)
        if exutil.verbLevel >= 2:
            self.mgr.summarize()
        
    def variables(self):
        return self.permuter.rpermute(range(1, self.ndata+1))

    # Extract constraints from BDD root
    # Return (phases, lb, ub)
    def findConstraints(self, root):
        phases = []
        cl = CardLayer(self.mgr, [root])
        exutil.eprint("Level 0.  Nodes=%s" % (str(cl)), 3)
        dvars = self.variables()
        exutil.eprint("Ordering data variables as %s" % dvars, 2)
        idList = dvars[1:] + [root.variable.leafLevel]
        for dv in dvars:
            cl, phase = cl.extend(dv)
            if cl is None:
                break
            exutil.eprint("Root Id %d.  Phase = %d, Nodes=%s" % (dv, phase, str(cl)), 4)
            phases.append(phase)
        if cl is None:
            exutil.eprint("Failed to extend layer", 3)
            return (None, None, None)
        lb, ub = cl.check()
        if lb is None:
            exutil.eprint("Final check failed", 3)
            return (None, None, None)
        else:
            exutil.eprint("BDD encodes constraint L=%d, U=%d, phases = %s" % (lb, ub, str(phases)), 3)
            return (phases, lb, ub)

    def getConstraints(self, phases, lb, ub):
        result = []
        if lb > ub:
            # Unsatisfiable
            result.append(Constraint([], 1))
            return result
        if lb > 0:
            # Nontrivial lower bound
            lits = [v if phase == 1 else -v for v,phase in zip(self.variables(), phases)]
            result.append(Constraint(lits, lb))
        if ub < self.ndata:
            # Nontrivial upper bound.  Must invert
            lits = [v if phase == 0 else -v for v,phase in zip(self.variables(), phases)]
            bound = self.ndata-ub
            result.append(Constraint(lits, bound))
        if exutil.verbLevel >= 2:
            exutil.eprint("Generated %d constraints:" % len(result), 2)
            for con in result:
                exutil.eprint(con.knfString(), 2)
        return result

    def getEncodingId(self, node):
        idList = self.permuter.rpermute(self.mgr.getSupportIds(node))
        eid = 0
        for id in idList:
            if id > self.ndata:
                eid = id
                break
        exutil.eprint("Selected top-level id %d from choices: %s" % (eid, str(idList)), 4)
        return eid

    # Root generator for garbage collection
    def checkBuckets(self):
        rootList = []
        for bucket in self.buckets.values():
            rootList += bucket
        return rootList

    # Check for GC and whether have exceeded resource bounds
    # Based on size of BDD
    def checkStatus(self, bddSize):
        if bddSize > maxBddSize:
            exutil.eprint("Aborting BDD construction.  BDD size = %d" % bddSize, 3)
            return False
        return True

    def generateBdd(self):
        self.encodingIds = self.permuter.rpermute(range(self.ndata+1, self.creader.nvar+1))
        self.buckets = { eid : [] for eid in self.encodingIds }
        self.buckets[0] = []

        # Build BDD representations of clauses and put in bucket according to highest encoding Id
        exutil.eprint("Generating BDD from CNF with %d program variables, %d encoding variables, and %d clauses" % 
                      (self.ndata, self.creader.nvar-self.ndata, len(self.creader.clauses)), 3)
        cid = 0
        for iclause in self.creader.clauses:
            cid += 1
            clause = [self.litMap[ilit] for ilit in iclause]
            try:
                node = self.mgr.buildClause(clause)
            except bdd.BddAbort as ex:
                exutil.eprint(str(ex), 3)
                return None
            eid = self.getEncodingId(node)
            self.buckets[eid].append(node)
            exutil.eprint("Clause #%d.  Root %s.  Bucket %d" % (cid, str(node), eid), 4)
        # Bucket elimination
        for eid in self.encodingIds + [0]:
            exutil.eprint("Id %d.  Conjoining %d nodes" % (eid, len(self.buckets[eid])), 4)
            while len(self.buckets[eid]) > 1:
                arg1 = self.buckets[eid][0]
                arg2 = self.buckets[eid][1]
                self.buckets[eid] = self.buckets[eid][2:]
                try:
                    prod = self.mgr.applyAnd(arg1, arg2)
                except bdd.BddAbort as ex:
                    exutil.eprint(str(ex), 3)
                    return None
                if not self.checkStatus(self.mgr.getSize(prod)):
                    return None
                peid = self.getEncodingId(prod)
                self.buckets[peid].append(prod)
                deadCount = self.mgr.getSize(arg1) + self.mgr.getSize(arg2)
                self.mgr.checkGC(deadCount)
            if len(self.buckets[eid]) == 1 and eid > 0:
                lit = self.litMap[eid]
                arg = self.buckets[eid][0]
                self.buckets[eid] = []
                try:
                    qval = self.mgr.equant(arg, lit)
                except bdd.BddAbort as ex:
                    exutil.eprint(str(ex), 3)
                    return None
                if not self.checkStatus(self.mgr.getSize(qval)):
                    return None
                qeid = self.getEncodingId(qval)
                exutil.eprint("Id %d.  Quantifying node %s gives node %s at id %d" % (eid, str(arg), str(qval), qeid), 4)
                self.buckets[qeid].append(qval)
                deadCount = self.mgr.getSize(arg)
                self.mgr.checkGC(deadCount)
        root = self.buckets[0][0]
        return root
        

def run(name, argList):
    random.seed(seed)
    cnfName = None
    n = None
    optlist, args = getopt.getopt(argList, "hv:i:n:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            exutil.setVerbLevel(int(val))
        elif opt == '-i':
            cnfName = val
        elif opt == '-n':
            n = int(val)
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    if cnfName is None:
        print("ERROR: Must give name of CNF file")
        usage(name)
        return

    start = datetime.datetime.now()
    try:
        creader = exutil.CnfReader(cnfName)
    except Exception as ex:
        print("Couldn't process CNF file '%s' (%s)" % (cnfName, str(ex)))
        return
    e = Extractor(creader, n)
    if e.success:
        print("SUCCESS:")
        for con in e.constraints:
            print("  " + con.knfString())
    else:
        print("FAILURE")
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    exutil.eprint("Elapsed seconds: %.2f" % (seconds), 2)
        

if __name__ == "__main__":
    # Increase maximum recursion depth
    sys.setrecursionlimit(10 * sys.getrecursionlimit())
    run(sys.argv[0], sys.argv[1:])
        
