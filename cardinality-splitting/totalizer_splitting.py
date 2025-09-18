import sys
import getopt
import random
import math

'''
Encode a totalizer tree in CNF from a KNF input formula.

Options:
  -f <file> : input file in KNF format
  -o <file> : output file in CNF format
  -m        : use AMK if it creates a smaller encoding
  -s        : print variable semantics
  -i <nCubes> : number of splitting variables (2^i cubes)

Example Run:

  python3 totalizer_splitting.py -f form.knf -o form.cnf

# to generate cubes while encoding
  python3 totalizer_splitting.py -f form.knf -i <nCubes> -o form.incf


'''



def all_combos (n):
  if n > 0: return [[1] + end for end in all_combos (n-1)]+[[-1] + end for end in all_combos (n-1)]
  else: return [[]]

class Totalizer:

  def __init__(self, alyways_ALK=True, all_totalizer=False):
    self.all_totalizer = all_totalizer
    self.always_ALK = alyways_ALK
    self.cube_vars = []
    self.cubes = []

  '''
    Print the semantics of the variables in the totalizer tree.
  '''
  def print_variable_semantics (self, totalizer):
    layers = totalizer['layers']
    nodes = totalizer['nodes']

    print(f"\nTotalizer with {len(layers)} layers:\n")
    for l in layers:
      for n in l:
        print(f"Node {n} {nodes[n]}")

    print(f"\nTotalizer auxiliary variables:\n")
    for v,d in totalizer['vars'].items():
      print(f"Var {v} : {d}")

  '''
    Return the first counter after the actual percent.

    Could also be closest to percent, or first before percent (above=True).
  '''
  def get_counter (self, node, actual_percent, above=True):
    nCounters = len(node['counters'])
    best_id = 1
    for i in range(1,nCounters+1):
      percent = float(i) / nCounters
      if percent >= actual_percent: 
        if above: 
          best_id = i
        break
      best_id = i
      
    print(f"picking {best_id} of {nCounters}, Var: {node['counters'][best_id-1]}")
    return node['counters'][best_id-1]

  '''
    Generate list of cubes from a set of variables, i.e.,
    all possible combinations of alternating 1/0.
  '''
  def generate_cubes (self, vars):
    cubes = []
    for c in (all_combos (len(vars))):
      cubes.append([c[i]*vars[i] for i in range(len(vars))])

    return cubes 

  '''
    Generate cubes for first cardinality constraint given totalizer tree.
  
    nCubes is the number of aux variables to select starting from the 
    second layer (first layer cannot be split because it has the actual bound/unit).
  '''
  def get_some_cube_vars (self, t, nCubes):
    # assuming we are picking only the first klause
    lits = t['lits']
    bound = t['bound']
    actual_percent = float(bound)/len(lits)

    cube_vars = []

    print(f"c Actual Percent: {round(actual_percent,2)}")

    # loop over nodes at each depth and get counter
    print(f"Number of layers: {len(t['layers'])}")

    roundUp =True
    for i in range(2,len(t['layers'])):
      layer_vars = []

      node_sort = sorted (t['layers'][i], key=lambda x: len(t['nodes'][x]['counters']),reverse=True)
      
      layer_sum = sum([math.ceil(len(t['nodes'][n]['counters'])*actual_percent) for n in t['layers'][i]])
      
      diff = bound - layer_sum
      print(f"Layer {i} has {len(t['layers'][i])} nodes, sum {layer_sum}, diff {diff}")

      for nCnt in range(0,len(node_sort),1):
        n = node_sort[nCnt]
        h = int(len(t['nodes'][n]['counters']) * actual_percent)
        
        if roundUp:
          h = h+1
        roundUp = not roundUp

        pos = -1
        if h < len(t['nodes'][n]['counters']):
          layer_vars += [t['nodes'][n]['counters'][h]]
          pos = h
        else:
          layer_vars += [t['nodes'][n]['counters'][h-1]]
          pos = h-1
        
        print(f"Selected pos {pos} from {len(t['nodes'][n]['counters'])}")
        print(f"Var {layer_vars[-1]} from counter {t['nodes'][n]['counters']}")
      
      cube_vars += layer_vars
      if len(cube_vars) >= nCubes :
        cube_vars = cube_vars[:nCubes]
        break

    self.cube_vars += cube_vars
    print(f"Selected subset {(cube_vars)} variables for cubes")

  '''
    Generate cubes for first cardinality constraint given totalizer tree.
  
    nCubes is the number of aux variables to select starting from the 
    second layer (first layer cannot be split because it has the actual bound/unit).
  '''
  def get_cube_vars (self, nCubes):

    per_total = int(nCubes/len(self.totalizers))
    if per_total < 1: per_total = 1
    for t in self.totalizers:
      self.get_some_cube_vars (t, per_total)
      if len(self.cube_vars) >= nCubes:
        self.cube_vars = self.cube_vars[:nCubes]
        break
    
    print(f"Selected {(self.cube_vars)} variables for cubes")
    self.cubes += self.generate_cubes (self.cube_vars)


  def write_cubes (self, out_file):
    for c in self.cubes:
      out_file.write ("a "+' '.join([str(l) for l in c])+" 0\n")

  def write_formula_clauses (self, out_file, incf):
    nClauses = 0
    nClauses += len(self.clauses) + len(self.klauses)
    for t in self.totalizers:
      nClauses += len(t['clauses'])
    maxVar = self.maxVar

    if incf: out_file.write(f"p inccnf\n")
    else: 
      out_file.write(f"p cnf {maxVar} {nClauses}\n")
    for c in self.clauses:
      out_file.write(f"{' '.join([str(l) for l in c])} 0\n")
    for bound,lits in self.klauses: 
      out_file.write(f"k {bound} {' '.join([str(l) for l in lits])} 0\n")
    for t in self.totalizers:
      for c in t['clauses']:
        out_file.write(f"{' '.join([str(l) for l in c])} 0\n")

  def write_formula (self, out_file, incf=False):
    o_file = open(out_file, 'w')
    
    self.write_formula_clauses (o_file, incf)

    o_file.close()

  def write_cube_file (self, out_file, nCubes, whole_formula):
    o_file = open(out_file, 'w')

    self.write_formula_clauses (o_file, True)

    self.nCubes = nCubes

    self.get_cube_vars (nCubes)
    self.write_cubes (o_file)

    o_file.close()


  '''
    Generate the tree and the clauses separately.
    The tree can be used for generating cubes or partial encodings.
  '''

  def clauses_for_totalizer(self, left, right, new_vars, bound, ALK):
    clauses = []
    needsUnit = False

    # print(f"{left} {right} {new_vars} {bound} {ALK}")

    nNewVars = len(new_vars)
    new_max_var = new_vars[-1]
    if not ALK and nNewVars == bound + 1: 
        needsUnit = True

    if ALK or self.all_totalizer > 0:
      # backwards clauses
      # 0 + 0 = 0, 1 + 1 >= 1
      clauses.append ([-new_vars[0], left[0], right[0]])

      # 0 + n = n, 1 + n + 1 >= n + 1
      if len(left) > 0:
        for l in range(1,len(left)+1):
          if l >= bound : # possible? would be unit false if AMK anyways
            continue
          if (l == len(left)):
            clauses.append ([-new_vars[l], right[0]])
          else:
            clauses.append ([-new_vars[l], left[l], right[0]])

      # n + 0 = n, n + 1 + 1 >= n + 1
      if len(right) > 0:
        for r in range(1,len(right)+1):
          if r >= bound : # possible?
            continue
          if (r == len (right)):
            clauses.append ([-new_vars[r], left[0]])
          else:
            clauses.append ([-new_vars[r], right[r], left[0]])

      # l>0,r>0, l + r = s, l+1 + r + 1 >= s + 1
      for l in range(len(left)):
        for r in range(len(right)):
          sum = l + r + 2 + 1
          if (sum > bound): 
            continue
          if l + 1 == len(left) and r + 1 == len(right):
            continue
          if (l + 1 == len(left)):
            clauses.append ([-new_vars[sum-1], right[r+1]])
          elif (r + 1 == len(right)):
            clauses.append ([-new_vars[sum-1], left[l+1]])
          else:
            clauses.append ([-new_vars[sum-1], left[l+1], right[r+1]])

            
    
    # forwards clauses
        
    if not ALK or self.all_totalizer > 0:
      for l in range(len(left)):
        if ALK and l > bound:
          continue
        if l > bound + 1:
          continue
        clauses.append ([new_vars[l], -left[l]])

      for r in range(len(right)):
        if ALK and r > bound:
          continue
        if r > bound + 1:
          continue
        clauses.append ([new_vars[r], -right[r]])

      for l in range(len(left)):
        for r in range(len(right)):
          sum = l + r + 2
          if ALK and sum > bound:
            continue
          if (sum > bound + 1): 
            continue
          clauses.append ([new_vars[sum-1], -left[l], -right[r]])

    # implication of sums
    for i in range(len(new_vars)-1):
      clauses.append ([new_vars[i], -new_vars[i+1]])

    # add unit clause if necessary
    if needsUnit:
      clauses.append([-new_max_var])
      new_vars = new_vars[:-1]

    return clauses, new_vars

  def totalizer_layer (self, bound, curr_layer, max_var, ALK, node_cnt, data, nodes, clauses):
  
    new_layer = []
    new_max_var = max_var

    nGroups = int (len(curr_layer)/2)

    for group in range(nGroups):

      firstIdx = group * 2

      left = curr_layer[firstIdx]
      right = curr_layer[firstIdx+1]

      nNewVars = len(left[0]) + len(right[0])
      new_vars = []
      if ALK:
        if nNewVars > bound: 
          nNewVars = bound
      else:
        if nNewVars > bound + 1: 
          nNewVars = bound + 1

      for i in range(nNewVars):
          new_vars.append(new_max_var+1)

          data[new_max_var+1] = {'cnt':i+1, 'node':node_cnt, 'tot':(nNewVars), 'per':{round(float(i+1)/nNewVars,3)}}

          new_max_var += 1

      # Clauses here; new_vars may change for AMK if you are counting to bound + 1
      node_clauses, new_vars = self.clauses_for_totalizer (left[0], right[0], new_vars,bound, ALK)
      clauses += node_clauses
      
      new_node = new_vars
      new_layer.append ((new_node, node_cnt))

      nodes[node_cnt] = {'left':left[1], 'right':right[1], 'counters':new_vars}

      node_cnt += 1

    # stragler
    if len(curr_layer) % 2 == 1:
      last_node = curr_layer[-1]
      last_processed_node = new_layer[-1]

      left = last_processed_node
      right = last_node
      

      nNewVars = len(left[0]) + len(right[0])
      new_vars = []
      if ALK:
        if nNewVars > bound: 
          nNewVars = bound
      else:
        if nNewVars > bound + 1: 
          nNewVars = bound + 1

      for i in range(nNewVars):
        new_vars.append(new_max_var+1)

        data[new_max_var+1] = {'cnt':i+1, 'node':node_cnt, 'tot':(nNewVars), 'per':{round(float(i+1)/nNewVars,3)}}

        new_max_var += 1

      # Clauses here; new_vars may change for AMK if you are counting to bound + 1
      node_clauses, new_vars = self.clauses_for_totalizer (left[0], right[0], new_vars, bound, ALK)
      clauses += node_clauses
      
      new_node = new_vars

      nodes[node_cnt] = {'left':left[1], 'right':right[1], 'counters':new_vars}

      new_layer[-1] = (new_node, node_cnt)

      node_cnt += 1

    return new_layer, new_max_var, node_cnt

  def encode_totalizer (self, bound, lits, max_var, ALK):
    data = {}
    nodes = {}
    layers = []
    node_cnt = 0
    clauses = []

    new_max_var = max_var
    layer_cnt = 0

    seen = {}
    next_layer = []
    for l in lits:
      next_layer.append (([l],node_cnt))
      seen[node_cnt] = 1
      node_cnt += 1

    while len(next_layer) > 1:
      next_layer, new_max_var, node_cnt = self.totalizer_layer (bound, next_layer, new_max_var, ALK, node_cnt, data, nodes, clauses)
      layer_cnt += 1

    # Generate depth for each node in tree starting from the root.
    # Can't do this in the previous loop because we don't know the depth of the nodes until the tree is built. Reason for this is the tree is not balanced (stragglers get merged).
    frontier = [node_cnt - 1]
    depth = 0

    layers = []
    var_data = {}
    
    while len(frontier) > 0:
      next_frontier = []
      layers.append(frontier.copy())
      for node_id in frontier:
        node = nodes[node_id]
        nodes[node_id]['depth'] = depth
        c = 1
        for l in node['counters']:
          var_data[abs(l)] = {'cnt':c,'depth':depth,'node':node_id}
          c+=1
        if node['left'] not in seen:
          next_frontier.append(node['left'])
          seen[node['left']] = 1
        if node['right'] not in seen:
          next_frontier.append(node['right'])
          seen[node['right']] = 1
      depth += 1
      frontier = next_frontier.copy()

    if ALK:
    # Add unit at the top of the encoding.
    # Must be last new variable (if not AMK), enforced the lower bound.
      clauses.append([new_max_var])

    data['clauses'] = clauses
    data['nodes']   = nodes
    data['layers']  = layers
    data['vars']    = var_data
    data['lits']    = lits
    data['bound']   = bound

    return data, new_max_var

    

  def parse_knf (self, in_file, randomize):
    in_formula = open(in_file, 'r')
    clauses = []
    klauses = []
    totalizers = []
    maxVar = -1

    for line in in_formula:
      tokens = line.split()
      if len(tokens) < 1: continue
      if tokens [0] == 'c': continue
      if tokens[0] == 'p': # header
        maxVar = int(tokens[2])
        nCls  = int(tokens[3])
        self.oMaxVar = maxVar
      elif tokens[0] == 'k': # klause
          bound = int(tokens[1])
          lits = [int (t) for t in tokens[2:-1]]
          if randomize > 0:
            random.shuffle(lits)
          if bound == 2 or bound == len(tokens) - 3:
            # AL2 - just use knf2cnf
            klauses.append((bound,lits))
          elif bound == len(tokens) - 4:
            # AMO - just use knf2cnf
            klauses.append((bound,lits))
          else: # general ALK - convert to totalizer
            # Decide if you will use ALK or AMK
            ALK = True # Default ALK for now
            if not self.always_ALK:
              if bound > len(lits)/2:
                ALK = False
              if not ALK: # flip the sign to <=
                bound = len(lits) - bound
                lits = [-l for l in lits]
            d, newMaxVar = self.encode_totalizer (bound, lits, maxVar, ALK)
            maxVar = newMaxVar # update maxVar
            totalizers.append(d)
      else: # clause
        clauses.append([int (t) for t in tokens[:-1]])

    self.clauses = clauses 
    self.klauses = klauses
    self.totalizers = totalizers
    self.maxVar = maxVar

    in_formula.close()

  def add_knf (self, in_file):
    self.parse_knf (in_file)
    
    
def run(name, args):
    in_file = None
    out_file = None
    print_semantics = False
    nCubes = 0
    all_totalizer = False
    randomize = -1
    always_ALK = False

    optlist, args = getopt.getopt(args, "hlpmszg:f:c:t:e:o:i:r:")
    for (opt, val) in optlist:
        if opt == '-f':
          in_file = val
        elif opt == '-o':
          out_file = val
        elif opt == '-m':
          always_ALK = False
        elif opt == '-l':
          always_ALK = True
        elif opt == '-s':
          print_semantics = True
        elif opt == '-p':
           all_totalizer = True
        elif opt == '-i':
          nCubes = int(val)
        elif opt == '-r':
          randomize = int(val)
        elif opt == '-h':
          print ("Usage: python3 totalizer_splitting.py -f <infile> -o <outfile> [-i <n splitting variables] ")
          exit(0)

    if randomize > 0:
      random.seed(randomize)
    else:
      random.seed(0)

    if in_file is not None:
      t = Totalizer(always_ALK,all_totalizer)
      t.parse_knf (in_file,randomize)
      if print_semantics:
        t.print_variable_semantics (t.totalizers[0])
      if nCubes == 0 and out_file is not None:
        t.write_formula (out_file, False)
      elif nCubes > 0 and out_file is not None:
        t.write_cube_file (out_file, nCubes, whole_formula=True)
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
