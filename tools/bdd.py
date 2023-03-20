# Implementation of simple BDD package

#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
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

from functools import total_ordering

import sys
import resolver

class BddException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "BDD Exception: " + str(self.value)

class BddAbort(Exception):
    
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return "BDD Abort: " + str(self.value)


# Place holder to allow program to run without proving anything
class DummyProver:

    clauseCount = 0
    writer = None
    verbLevel = 0

    def __init__(self, fname = None, verbLevel = None):
        self.clauseCount = 0
        self.writer = sys.stderr

    def comment(self, comment):
        pass

    def createClause(self, result, antecedent, comment = None, isInput = False, alreadyClean = False):
        if not alreadyClean:
            result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            return result
        self.clauseCount += 1
        return self.clauseCount

    def emitProof(self, proof, ruleIndex, comment = None):
        self.clauseCount += 1
        return self.clauseCount

    def fileOutput(self):
        return False

    def summarize(self):
        pass

@total_ordering
class Variable:
    name = None
    level = 0  # For ordering
    leafLevel = -1 # Special value
    id = None # Serves as identity of resolution variable

    def __init__(self, level, name = None, id = None):
        self.level = level
        if id is None:
            self.id = level
        elif level == self.leafLevel:
            self.id = 0
        else:
            self.id = id
        if name is None:
            name = "var-%d" % level
        self.name = str(name)

    def __eq__(self, other):
        return self.level == other.level

    def __ne__(self, other):
        return self.level != other.level

    def __lt__(self, other):
        # Check for leaves
        if self.level == self.leafLevel:
            return False
        if other.level == self.leafLevel:
            return True
        return self.level < other.level

    def __hash__(self):
        return hash(self.level)

    def __str__(self):
        return self.name


class Node:
    id = 0 # Also serves as identity of ER variable
    variable = None

    def __init__(self, id, variable):
        self.id = id
        self.variable = variable
    
    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id

    def label(self):
        return "N%d" % self.id

    def clauses(self, prover):
        return []

    def clauseIds(self):
        return []

    def isZero(self):
        return False

    def isOne(self):
        return False


class LeafNode(Node):
    value = None # 0 or 1
    inferValue = None # Number of unit clause asserting its value

    def __init__(self, value):
        id = resolver.tautologyId if value == 1 else -resolver.tautologyId        
        Node.__init__(self, id, Variable(Variable.leafLevel, "Leaf"))
        self.value = value
        self.inferValue = self.id

    def isLeaf(self):
        return True

    def label(self):
        return "C%d" % self.value

    def isZero(self):
        return self.value == 0

    def isOne(self):
        return self.value == 1
    
    def __str__(self):
        return "leaf-%d" % self.value


class VariableNode(Node):
    # Defining clause types
    (HU, LU, HD, LD) = range(4)
    high = None
    low = None
    # Identity of clauses generated from node
    definingClauseBase = 0
    
    def __init__(self, id, variable, high, low, prover):
        Node.__init__(self, id, variable)
        self.high = high
        self.low = low
        vid = self.variable.id
        hid = self.high.id
        lid = self.low.id
        # id should be first literal in clause for some proof checkers
        label = "node %s = ITE(%s,%s,%s)"  % (self.label(), str(self.variable), self.high.label(), self.low.label())
            
        antecedents = []
        comment = "ITE assertions for %s" % label
        if prover.verbLevel >= 3:
            comment = "ITE assertion for %s: HU" % label
        huid = prover.createClause(self.clauseHU(), [], comment, alreadyClean = True)
        if huid != resolver.tautologyId:
            comment = None
            antecedents.append(-huid)
            if self.definingClauseBase == 0:
                self.definingClauseBase = huid - self.HU
        
        if prover.verbLevel >= 3:
            comment = "ITE assertion for %s: LU" % label
        luid = prover.createClause(self.clauseLU(), [], comment, alreadyClean = True)
        if luid != resolver.tautologyId:
            comment = None
            antecedents.append(-luid)
            if self.definingClauseBase == 0:
                self.definingClauseBase = luid - self.LU

        if prover.verbLevel >= 3:
            comment = "ITE assertion for %s: HD" % label
        hdid = prover.createClause(self.clauseHD(), antecedents, comment, alreadyClean = True)
        if hdid != resolver.tautologyId:
            comment = None
            if self.definingClauseBase == 0:
                self.definingClauseBase = hdid - self.HD

        if prover.verbLevel >= 3:
            comment = "ITE assertion for %s: LD" % label
        ldid = prover.createClause(self.clauseLD(), antecedents, comment, alreadyClean = True)
        if ldid != resolver.tautologyId:
            comment = None
            if self.definingClauseBase == 0:
                self.definingClauseBase = ldid - self.LD
    
    def isLeaf(self):
        return False

    def clauseHU(self):
        id = self.id
        vid = self.variable.id
        hid = self.high.id
        lid = self.low.id
        return resolver.cleanClause([id, -vid, -hid])

    def clauseLU(self):
        id = self.id
        vid = self.variable.id
        hid = self.high.id
        lid = self.low.id
        return resolver.cleanClause([id, vid, -lid])

    def clauseHD(self):
        id = self.id
        vid = self.variable.id
        hid = self.high.id
        lid = self.low.id
        return resolver.cleanClause([-id, -vid, hid])

    def clauseLD(self):
        id = self.id
        vid = self.variable.id
        hid = self.high.id
        lid = self.low.id
        return resolver.cleanClause([-id, vid, lid])

    def idHU(self):
        return resolver.tautologyId if self.high.isZero() else self.definingClauseBase + self.HU

    def idLU(self):
        return resolver.tautologyId if self.low.isZero() else self.definingClauseBase + self.LU

    def idHD(self):
        return resolver.tautologyId if self.high.isOne() else self.definingClauseBase + self.HD

    def idLD(self):
        return resolver.tautologyId if self.low.isOne() else self.definingClauseBase + self.LD

    def branchHigh(self, variable):
        if self.variable < variable:
            raise BddException("Node at level %d cannot branch on variable at level %d" % 
                               (self.variable.level, variable.level))
        if self.isLeaf():
            return self
        elif self.variable == variable:
            return self.high
        else:
            return self

    def branchLow(self, variable):
        if self.variable < variable:
            raise BddException("Node at level %d cannot branch on variable at level %d" % 
                               (self.variable.level, variable.level))
        if self.isLeaf():
            return self
        elif self.variable == variable:
            return self.low
        else:
            return self
        
    # Return list of defining clause Ids
    def clauseIds(self, up=True, down=True):
        idList = []
        if up:
            idList += [self.idHU(), self.idLU()]
        if down:
            idList += [self.idHD(), self.idLD()]
        idList = [id for id in idList if (id is not None and id != resolver.tautologyId)]
        return idList

    # Return list of defining clauses
    def clauses(self, prover, up=True, down=True):
        idlist = self.clauseIds(up, down)
        return [prover.clauseDict[id] for id in idlist]

    def __str__(self):
        return "%d:%s->%s,%s" % (self.id, str(self.variable), self.high.label(), self.low.label())

class Manager:
    prover = None
    writer = None
    # List of variables, ordered by level
    variables = []
    nextNodeId = 0
    # Leaf nodes
    leaf0 = None
    leaf1 = None
    # Mapping from (variable, high, low) to node
    uniqueTable = {}
    # Operation cache
    # Key = (opName, operand1 ...) to (node, justification)
    # Hack: justification is negative when preceding clause was generated as intermediate step
    operationCache = {}
    verbLevel = 1
    resolver = None
    # GC support
    # Callback function from driver that will collect accessible roots for GC
    rootGenerator = None
    # Estimate of number of dead nodes (possibly overestimates)
    deadNodeCount = 0
    # How many dead nodes as fraction of live nodes to trigger GC
    gcFraction = 0.20
    # Minimum number of nodes before trigger GC
    gcMin = 10000
    # Dictionary mapping variables to their IDs
    quantifiedVariableSet = None
    # Rule to give up
    liveCountLimit = None
    # Statistics
    cacheJustifyAdded = 0
    cacheNoJustifyAdded = 0
    applyCount = 0
    nodeCount = 0
    maxLiveCount = 0
    variableCount = 0
    cacheRemoved = 0
    nodesRemoved = 0
    gcCount = 0


    def __init__(self, prover = None, rootGenerator = None, nextNodeId = 0, verbLevel = 1):

        self.verbLevel = verbLevel
        self.prover = DummyProver() if prover is None else prover
        self.writer = self.prover.writer
        self.rootGenerator = rootGenerator
        self.variables = []
        self.leaf0 = LeafNode(0)
        self.leaf1 = LeafNode(1)
        self.nextNodeId = nextNodeId
        self.uniqueTable = {}
        self.operationCache = {}
        self.vresolver = resolver.VResolver(self.prover)
        self.quantifiedVariableSet = set([])
        self.liveCountLimit = None
        self.deadNodeCount = 0
        self.cacheJustifyAdded = 0
        self.cacheNoJustifyAdded = 0
        self.applyCount = 0
        self.nodeCount = 0
        self.maxLiveCount = 0
        self.variableCount = 0
        self.cacheRemoved = 0
        self.nodesRemoved = 0
        self.gcCount = 0

    def newVariable(self, name, id = None):
        level = len(self.variables) + 1
        var = Variable(level, name, id)
        self.variables.append(var)
        self.variableCount += 1
        return var
        
    def setLimit(self, size):
        self.liveCountLimit = size

    def findOrMake(self, variable, high, low):
        key = (variable.level, high.id, low.id)
        if key in self.uniqueTable:
            return self.uniqueTable[key]
        else:
            node = VariableNode(self.nextNodeId, variable, high, low, self.prover)
            self.nextNodeId += 1
            self.uniqueTable[key] = node
            self.nodeCount += 1
            liveCount = len(self.uniqueTable)
            if self.liveCountLimit is not None and liveCount > self.liveCountLimit:
                raise BddAbort("Live count limit %d exceeded" % self.liveCountLimit)
            self.maxLiveCount = max(self.maxLiveCount, liveCount)
            return node
  
    def literal(self, variable, phase):
        if phase == 1:
            return self.findOrMake(variable, self.leaf1, self.leaf0)
        else:
            return self.findOrMake(variable, self.leaf0, self.leaf1)

    def buildClause(self, literalList):
        lits = sorted(literalList, key=lambda n: -n.variable.level)
        return self.reduceList(lits, self.applyOr, self.leaf0)

    def constructClause(self, clauseId, literalList):
        root = self.buildClause(literalList)
        lits = self.deconstructClause(root)
        # List antecedents in reverse order of resolution steps
        antecedents = []
        for node in lits:
            positive = node.high == self.leaf1
            if positive:
                antecedents.append(node.idHU())
                if node.low != self.leaf0:
                    antecedents.append(node.idLU())
            else:
                antecedents.append(node.idLU())
                if node.high != self.leaf0:
                    antecedents.append(node.idHU())
        antecedents.append(clauseId)
        validation = self.prover.createClause([root.id], antecedents, "Validate BDD representation of clause %d" % clauseId)
        return root, validation
    
    def deconstructClause(self, clause):
        lits = []
        while not clause.isLeaf():
            positive = clause.high == self.leaf1
            lits.append(clause)
            clause = clause.low if positive else clause.high
        return lits

    # Build dictionary mapping nodes in DAG rooted by node to values
    # nodeFunction should be a function mapping a node to a value
    def buildInformation(self, node, nodeFunction, sofarDict):
        if node in sofarDict:
            return sofarDict
        sofarDict[node] = nodeFunction(node)
        if node.isLeaf():
            return sofarDict
        else:
            sofarDict = self.buildInformation(node.high, nodeFunction, sofarDict)
            return self.buildInformation(node.low, nodeFunction, sofarDict)
        
    # Find support for function rooted by node.  Return as clause
    def getSupport(self, node):
        varDict = self.buildInformation(node, lambda n: n.variable, {})
        fullList = sorted(varDict.values())
        vlist = []
        for v in fullList:
            if (len(vlist) == 0 or vlist[-1] != v) and v.level != Variable.leafLevel:
                vlist.append(v)
        lits = [self.literal(v, 1) for v in  vlist]
        return self.buildClause(lits)

    def getSupportIds(self, node):
        varDict = self.buildInformation(node, lambda n: n.variable.id, {})
        fullList = sorted(varDict.values())
        ilist = []
        for id in fullList:
            if (len(ilist) == 0 or ilist[-1] != id) and id > 0:
                ilist.append(id)
        return ilist

    def getSize(self, node):
        oneDict = self.buildInformation(node, lambda n: 1, {})
        return len(oneDict)

    def showLiteral(self, lit):
        positive = lit.high == self.leaf1
        prefix = ' ' if positive else '!'
        return prefix + str(lit.variable)

    def showLiterals(self, litList):
        return "(" + ''.join(self.showLiteral(l) for l in litList) + ")"

    def showLiteralList(self, litLL):
        return '[' + ', '.join(self.showLiterals(ls) for ls in litLL) + ']'

    # Count number of solutions to function
    # Over variables consisting of support set for function
    def satisfyCount(self, root):
        supportClause = self.getSupport(root)
        # Mapping from (node, support) to count
        countDict = {(self.leaf1, self.leaf0) : 1}
        count = self.countStep(root, supportClause, countDict)
        return count

    # Recursive step of solution counting
    def countStep(self, root, supportClause, countDict):
        if (root, supportClause) in countDict:
            return countDict[(root, supportClause)]
        if root == self.leaf0:
            countDict[(root, supportClause)] = 0
            return 0
        if supportClause == self.leaf0:
            msg = "Ran out of support variables with nonleaf root node %s" % (str(root))
            raise BddException(msg)
        varS = supportClause.variable
        varR = root.variable
        nsupport = supportClause.low
        if varS < varR:
            ncount = self.countStep(root, nsupport, countDict)
            count = 2 * ncount
        elif varS == varR:
            highR = root.high
            lowR =  root.low
            countH = self.countStep(highR, nsupport, countDict)
            countL = self.countStep(lowR, nsupport, countDict)
            count = countH + countL
        else:
            msg = "Node variable not in support set" % (str(root))
            raise BddException(msg)
        countDict[(root, supportClause)] = count
        return count

    # Return lists of literals representing all solutions
    def satisfy(self, node):
        if node.isLeaf():
            return [] if node.value == 0 else [[]]
        highList = self.satisfy(node.high)
        highPrefix = [self.literal(node.variable, 1)]
        highList = [highPrefix + ls for ls in highList]
        lowList = self.satisfy(node.low)
        lowPrefix = [self.literal(node.variable, 0)]
        lowList = [lowPrefix + ls for ls in lowList]        
        return  highList + lowList

    # Generate strings representing all possible solutions
    def satisfyStrings(self, node, limit = None):
        satList = self.satisfy(node)
        stringList = []
        for litList in satList:
            slist = ['-'] * len(self.variables)
            for lit in litList:
                positive = lit.high == self.leaf1
                slist[lit.variable.level-1] = '1' if positive else '0'
            stringList.append(''.join(slist))
            if limit is not None and len(stringList) >= limit:
                break
        return stringList

    # Retrieve item from cache.  Return None if not found
    def operationRetrieve(self, key):
        if key in self.operationCache:
            entry = self.operationCache[key]
            return (entry[0], abs(entry[1]))
        return None
     

    # Return node + id of clause justifying that nodeA & NodeB ==> result
    # Justification is None if it would be tautology
    def applyAndJustify(self, nodeA, nodeB):
        self.applyCount += 1
        # Constant cases.
        # No justifications required, since all return one of the arguments
        if nodeA == self.leaf0 or nodeB == self.leaf0:
            return (self.leaf0, resolver.tautologyId)
        if nodeA == self.leaf1:
            return (nodeB, resolver.tautologyId)
        if nodeB == self.leaf1:
            return (nodeA, resolver.tautologyId)
        if nodeA == nodeB:
            return (nodeA, resolver.tautologyId)

        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA
        key = ("and", nodeA.id, nodeB.id)
        lookup = self.operationRetrieve(key)
        if lookup is not None:
            return lookup

        # Mapping from rule names to pair (clause id, clause)
        hints = {}
        # Mapping from variable names to variable numbers
        splitVar = min(nodeA.variable, nodeB.variable)
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        if highA != lowA:
            hints["UHD"] = (nodeA.idHD(), resolver.cleanClause([-splitVar.id, -nodeA.id, highA.id]))
            hints["ULD"] = (nodeA.idLD(), resolver.cleanClause([ splitVar.id, -nodeA.id, lowA.id]))
        if highB != lowB:
            hints["VHD"] = (nodeB.idHD(), resolver.cleanClause([-splitVar.id, -nodeB.id, highB.id]))
            hints["VLD"] = (nodeB.idLD(), resolver.cleanClause([ splitVar.id, -nodeB.id, lowB.id]))

        (newHigh, andHigh) = self.applyAndJustify(highA, highB)
        hints["OPH"] = (andHigh, resolver.cleanClause([-highA.id, -highB.id, newHigh.id]))
            
        (newLow, andLow) = self.applyAndJustify(lowA, lowB)
        hints["OPL"] = (andLow, resolver.cleanClause([-lowA.id, -lowB.id, newLow.id]))

        if newHigh == newLow:
            newNode = newHigh
        else:
            newNode = self.findOrMake(splitVar, newHigh, newLow)
            hints["WHU"] = (newNode.idHU(), resolver.cleanClause([-splitVar.id, newNode.id, -newHigh.id]))
            hints["WLU"] = (newNode.idLU(), resolver.cleanClause([ splitVar.id, newNode.id, -newLow.id]))

        targetClause = resolver.cleanClause([-nodeA.id, -nodeB.id, newNode.id])
        if targetClause == resolver.tautologyId:
            justification = resolver.tautologyId
        else:
            comment = "Justification that %s & %s ==> %s" % (nodeA.label(), nodeB.label(), newNode.label())
            justification = self.vresolver.run(targetClause, splitVar.id, hints, comment)
        self.operationCache[key] = (newNode, justification)
        self.cacheJustifyAdded += 1
        return (newNode, abs(justification))

    def applyNot(self, node):
        # Constant case
        if node == self.leaf1:
            return self.leaf0
        if node == self.leaf0:
            return self.leaf1
        key = ("not", node.id)
        if key in self.operationCache:
            return self.operationCache[key][0]
        var = node.variable
        high = node.high
        low = node.low
        newHigh = self.applyNot(high)
        newLow = self.applyNot(low)
        newNode = self.findOrMake(var, newHigh, newLow)
        self.operationCache[key] = (newNode, resolver.tautologyId)
        return (newNode, resolver.TautologyId)

    def justifyImply(self, nodeA, nodeB):
        self.applyCount += 1

        # Special cases
        if nodeA == nodeB:
            return (True, resolver.tautologyId)
        if nodeA == self.leaf0:
            return (True, resolver.tautologyId)
        if nodeB == self.leaf1:
            return (True, resolver.tautologyId)
        # It would be an error if implication fails
        if nodeA == self.leaf1:
            return (False, resolver.tautologyId)
        if nodeB == self.leaf0:
            return (False, resolver.tautologyId)

        key = ("imply", nodeA.id, nodeB.id)
        lookup = self.operationRetrieve(key)
        if lookup is not None:
            return lookup

        # Mapping from rule names to pair (clause id, clause)
        hints = {}
        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        if highA != lowA:
            hints["UHD"] = (nodeA.idHD(), resolver.cleanClause([-splitVar.id, -nodeA.id, highA.id]))
            hints["ULD"] = (nodeA.idLD(), resolver.cleanClause([ splitVar.id, -nodeA.id, lowA.id]))
        if highB != lowB:
            hints["WHU"] = (nodeB.idHU(), resolver.cleanClause([-splitVar.id, nodeB.id, -highB.id]))
            hints["WLU"] = (nodeB.idLU(), resolver.cleanClause([ splitVar.id, nodeB.id, -lowB.id]))

        (check, implyHigh) = self.justifyImply(highA, highB)
        if implyHigh != resolver.tautologyId:
            hints["OPH"] = (implyHigh, resolver.cleanClause([-highA.id, highB.id]))

        if check:
            (check, implyLow) = self.justifyImply(lowA, lowB)
            if implyLow != resolver.tautologyId:
                hints["OPL"] = (implyLow, resolver.cleanClause([-lowA.id, lowB.id]))

        if check:
            targetClause = resolver.cleanClause([-nodeA.id, nodeB.id])
            comment = "Justification that %s ==> %s" % (nodeA.label(), nodeB.label())
            justification = self.vresolver.run(targetClause, splitVar.id, hints, comment)
        else:
            justification = resolver.tautologyId

        self.operationCache[key] = (check, justification)
        if justification != resolver.tautologyId:
            self.cacheJustifyAdded += 1
        else:
            self.cacheNoJustifyAdded += 1
        return (check, abs(justification))

    def checkImply(self, nodeA, nodeB):
        check, justification = justifyImply(nodeA, nodeB)
        return check


    # Compute conjunction of nodeA & nodeB, and check
    # that result implies nodeC.
    # Return check + proof step
    def applyAndJustifyImply(self, nodeA, nodeB, nodeC):
        self.applyCount += 1
        # Terminal cases.
        if nodeA == self.leaf0 or nodeB == self.leaf0:
            # 0 implies everything
            return (True, resolver.tautologyId)
        if nodeA == self.leaf1:
            return self.justifyImply(nodeB, nodeC)
        if nodeB == self.leaf1:
            return self.justifyImply(nodeA, nodeC)
        if nodeA == nodeB:
            return self.justifyImply(nodeA, nodeC)
        if nodeC == self.leaf1:
            return (True, resolver.tautologyId)

        if nodeA.id > nodeB.id:
            # Commute arguments
            nodeA, nodeB = nodeB, nodeA
        key = ("andimply", nodeA.id, nodeB.id, nodeC.id)
        lookup = self.operationRetrieve(key)
        if lookup is not None:
            return lookup

        # Mapping from rule names to pair (clause id, clause)
        hints = {}
        # Mapping from variable names to variable numbers
        splitVar = min(nodeA.variable, nodeB.variable)
        if nodeC != self.leaf0:
            splitVar = min(splitVar, nodeC.variable)
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)
        highC = nodeC if nodeC == self.leaf0 else nodeC.branchHigh(splitVar)
        lowC =  nodeC if nodeC == self.leaf0 else nodeC.branchLow(splitVar)

        if highA != lowA:
            hints["UHD"] = (nodeA.idHD(), resolver.cleanClause([-splitVar.id, -nodeA.id, highA.id]))
            hints["ULD"] = (nodeA.idLD(), resolver.cleanClause([ splitVar.id, -nodeA.id, lowA.id]))
        if highB != lowB:
            hints["VHD"] = (nodeB.idHD(), resolver.cleanClause([-splitVar.id, -nodeB.id, highB.id]))
            hints["VLD"] = (nodeB.idLD(), resolver.cleanClause([ splitVar.id, -nodeB.id, lowB.id]))
        if highC != lowC:
            hints["WHU"] = (nodeC.idHU(), resolver.cleanClause([-splitVar.id, nodeC.id, -highC.id]))
            hints["WLU"] = (nodeC.idLU(), resolver.cleanClause([ splitVar.id, nodeC.id, -lowC.id]))

        (check, implyHigh) = self.applyAndJustifyImply(highA, highB, highC)
        if implyHigh != resolver.tautologyId:
            hints["OPH"] = (implyHigh, resolver.cleanClause([-highA.id, -highB.id, highC.id]))

        if check:
            (check, implyLow) = self.applyAndJustifyImply(lowA, lowB, lowC)
            if implyLow != resolver.tautologyId:
                hints["OPL"] = (implyLow, resolver.cleanClause([-lowA.id, -lowB.id, lowC.id]))

        if check:
            targetClause = resolver.cleanClause([-nodeA.id, -nodeB.id, nodeC.id])
            if targetClause == resolver.tautologyId:
                justification = resolver.tautologyId
            else:
                comment = "Justification that %s & %s ==> %s" % (nodeA.label(), nodeB.label(), nodeC.label())
                justification = self.vresolver.run(targetClause, splitVar.id, hints, comment)
        else:
            justification = resolver.tautologyId, []

        self.operationCache[key] = (check, justification)
        if justification != resolver.tautologyId:
            self.cacheJustifyAdded += 1
        else:
            self.cacheNoJustifyAdded += 1
        return (check, abs(justification))

      
    # Version that runs without generating justification
    def applyAnd(self, nodeA, nodeB):
        self.applyCount += 1
        # Constant cases.
        if nodeA == self.leaf0 or nodeB == self.leaf0:
            return self.leaf0
        if nodeA == self.leaf1:
            return nodeB
        if nodeB == self.leaf1:
            return nodeA
        if nodeA == nodeB:
            return nodeA

        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA
        key = ("andnj", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key][0]

        # Mapping from variable names to variable numbers
        splitVar = min(nodeA.variable, nodeB.variable)
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        newHigh = self.applyAnd(highA, highB)
        newLow  = self.applyAnd(lowA, lowB)

        if newHigh == newLow:
            newNode = newHigh
        else:
            newNode = self.findOrMake(splitVar, newHigh, newLow)

        self.operationCache[key] = (newNode,resolver.tautologyId)
        return newNode


    def applyOr(self, nodeA, nodeB):
        # Constant cases
        if nodeA == self.leaf1:
            return self.leaf1
        if nodeB == self.leaf1:
            return self.leaf1
        if nodeA == self.leaf0:
            return nodeB
        if nodeB == self.leaf0:
            return nodeA
        if nodeA == nodeB:
            return nodeA
        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA
        key = ("or", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key][0]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        newHigh = self.applyOr(highA, highB)
        newLow = self.applyOr(lowA, lowB)
        newNode = newHigh if newHigh == newLow else self.findOrMake(splitVar, newHigh, newLow)
        self.operationCache[key] = (newNode,resolver.tautologyId)
        self.cacheNoJustifyAdded += 1
        return newNode


    # Given list of nodes, perform reduction operator (and, or, xor)
    def reduceList(self, nodeList, operator, emptyValue):
        fun = emptyValue
        for n in nodeList:
            fun = operator(fun, n)
        return fun

    # Use clause to provide canonical list of nodes.  Should all be positive
    def equant(self, node, clause, topLevel = True):
        if topLevel:
            nextc = clause
            while not nextc.isLeaf():
                self.quantifiedVariableSet.add(nextc.variable)
                nextc = nextc.low
        if node.isLeaf():
            return node
        while not clause.isLeaf() and node.variable > clause.variable:
            clause = clause.low
        if clause.isLeaf():
            return node
        key = ("equant", node.id, clause.id)
        
        if key in self.operationCache:
            return self.operationCache[key][0]

        newHigh = self.equant(node.high, clause, topLevel = False)
        newLow = self.equant(node.low, clause, topLevel = False)
        if newHigh == newLow:
            newNode = newHigh
        else:
            quant = node.variable == clause.variable
            newNode = self.applyOr(newHigh, newLow) if quant else self.findOrMake(node.variable, newHigh, newLow)
        self.operationCache[key] = (newNode, resolver.tautologyId)
        self.cacheNoJustifyAdded += 1
        return newNode
            
    # Generate list of all nodes from root.
    # Order according to postorder traversal of graph
    def getNodeList(self, node, includeLeaves = True):
        nset = set([])
        nlist = []
        def traverse(n):
            if n in nset:
                return
            if not n.isLeaf():
                traverse(n.high)
                traverse(n.low)
                nlist.append(n)
            elif includeLeaves:
                nlist.append(n)
            nset.add(n)
        traverse(node)
        return nlist

    # Generate clausal representation of BDD
    # Return as list of clauses
    def generateClauses(self, node, up=True, down=True):
        clauseList = []
        if node.isLeaf():
            nodeList = []
            if node == self.leaf0:
                clauseList.append([])
            rootid = 0 if node == self.leaf0 else 1
        else:
            nodeList = self.getNodeList(node, includeLeaves=False)
            for n in nodeList:
                clauseList += n.clauses(self.prover, up, down)
            # Assert output as unit clause
            clauseList.append([node.id])
        return clauseList

    # Should a GC be triggered?
    def checkGC(self, newDeadCount):
        self.deadNodeCount += newDeadCount
        liveNodeCount = len(self.uniqueTable)
        df = float(self.deadNodeCount) / liveNodeCount
        if liveNodeCount >= self.gcMin and df >= self.gcFraction:
            # Turn off trigger for garbage collection
            self.deadNodeCount = 0
            return self.collectGarbage()
        return []

    # Create set nodes that should not be collected
    # Maintain frontier of marked nonleaf nodes
    def doMarking(self, frontier):
        markedSet = set([])
        while len(frontier) > 0:
            node = frontier[0]
            frontier = frontier[1:]
            if node in markedSet:
                continue
            markedSet.add(node)
            if not node.high.isLeaf():
                frontier.append(node.high)
            if not node.low.isLeaf():
                frontier.append(node.low)
        return markedSet

    def cleanCache(self, markedSet):
        clauseList = []
        markedIds = set([node.id for node in markedSet])
        klist = list(self.operationCache.keys())
        for k in klist:
            kill = self.operationCache[k][0] not in markedSet
            # Skip over operation name
            for id in k[1:]:
                kill = kill or id not in markedIds
            if kill:
                cid = self.operationCache[k][1]
                if abs(cid) != resolver.tautologyId:
                    clist = [cid] if cid > 0 else [-cid-1, -cid]
                    clauseList += clist
                self.cacheRemoved += 1
                del self.operationCache[k]
        return clauseList
        
    def cleanNodes(self, markedSet):
        clauseList = []
        klist = list(self.uniqueTable.keys())
        for k in klist:
            node = self.uniqueTable[k]
            # If node is marked, then its children will be, too
            if node not in markedSet:
                clist = [node.idHU(), node.idLU(), node.idHD(), node.idLD()]
                clist = [c for c in clist if c != resolver.tautologyId]
                clauseList += clist
                self.nodesRemoved += 1
                del self.uniqueTable[k]
        return clauseList


    # Start garbage collection.
    # Provided with partial list of accessible roots
    def collectGarbage(self):
        oldCount = len(self.uniqueTable)
        frontier = []
        if self.rootGenerator is not None:
            frontier += self.rootGenerator()
        frontier = [r for r in frontier if (r is not None and not r.isLeaf())]
        # Marking phase
        markedSet = self.doMarking(frontier)
        clauseList = self.cleanCache(markedSet)
        clauseList += self.cleanNodes(markedSet)
        self.gcCount += 1
        newCount = len(self.uniqueTable)
        if self.verbLevel >= 3:
            self.writer.write("GC #%d %d --> %d nodes\n" % (self.gcCount, oldCount, newCount))
        return clauseList

    # Summarize activity
    def summarize(self):
        if self.verbLevel >= 1:
            self.writer.write("Input variables: %d\n" % self.variableCount)
            if self.verbLevel >= 2:
                self.writer.write("Variables quantified out: %d\n" % len(self.quantifiedVariableSet))
            self.writer.write("Total nodes: %d\n" % self.nodeCount)
            if self.verbLevel >= 2:
                self.writer.write("Total nodes removed by gc: %d\n" % self.nodesRemoved)
            self.writer.write("Maximum live nodes: %d\n" % self.maxLiveCount)
            self.writer.write("Total apply operations: %d\n" % self.applyCount)            
            if self.verbLevel >= 2:
                self.writer.write("Total cached results not requiring proofs: %d\n" % self.cacheNoJustifyAdded)
                self.writer.write("Total cached results requiring proofs: %d\n" % self.cacheJustifyAdded)
                self.writer.write("Total cache entries removed: %d\n" % self.cacheRemoved)
            self.writer.write("Total GCs performed: %d\n" % self.gcCount)
        if self.verbLevel >= 2:
            self.writer.write("Results from resolver:\n")
            self.vresolver.summarize()
        if self.verbLevel >= 1:
            self.writer.write("Results from proof generation\n")
            self.prover.summarize()
        
