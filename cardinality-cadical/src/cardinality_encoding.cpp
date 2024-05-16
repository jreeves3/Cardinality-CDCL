#include "internal.hpp"

namespace CaDiCaL {

// Cardinality Constraint (Re)Encoding to Clauses

// struct Cardinality_Constraint {
//   int card_idx;
//   vector<int> cls_idxs;
//   int first_aux;
//   int last_aux;
// };

void Cardinality_constraint::sort_unencoded_prob_vars () {
  vector<double> *temp_tab;
  int by_score = internal->opts.ccdclEncodingByScore;

  if (by_score == 1)temp_tab = &internal->stab;
  else if (by_score == 2) temp_tab = &internal->mptab;

  if (by_score) {

    // printf("PRE SORT\n");

    int mid = internal->sort_by_phase (unencoded_prob_vars);

    assert (mid <= unencoded_prob_vars.size());
    // printf("Mid %d size %d\n",mid,literals.size());

    if (mid > 1)
      sort (unencoded_prob_vars.begin(), unencoded_prob_vars.begin() + mid -1, [temp_tab] (const int &a, const int &b) {return temp_tab->at(abs (a)) > temp_tab->at(abs (b));} );
    if (mid < unencoded_prob_vars.size() - 1 )
      sort (unencoded_prob_vars.begin() + mid, unencoded_prob_vars.end (), [temp_tab] (const int &a, const int &b) {return temp_tab->at(abs (a)) > temp_tab->at(abs (b));} );

    //  // sort literals based on variable score
    // sort (literals.begin(), literals.end(), [temp_tab] (const int &a, const int &b) {return temp_tab->at(abs (a)) > temp_tab->at(abs (b));} );
  }
  else 
    sort (unencoded_prob_vars.begin(), unencoded_prob_vars.end(), [] (const int &a, const int &b) {return (abs (a)) < (abs (b));} );
}

// SPLIT (x1,...,xn) = AMO (x1,x2,x3,y1) /\ SPLIT (-y1,x4,...,xn)
int Internal::split_full_encoding (vector<int> lits, int start, int fresh_var, bool add_derivation) {
  int size = lits.size () - start;
  vector<int> temp_clause;

  int orig_size = encoding_clauses.size();
  
  // base cases
  if (size > 1) {
    encoding_clauses.push_back ({lits[start+0], lits[start+1]});
    // learn clause, add derivation, etc.
  }

  if (size > 2) {
    encoding_clauses.push_back ({lits[start+0], lits[start+2]});

    encoding_clauses.push_back ({lits[start+1], lits[start+2]});

  }


  if (size == 3) {
    if (add_derivation) {
    for (unsigned i = orig_size; i < encoding_clauses.size(); i++)
      encoding_derivation.push_back (encoding_clauses[i]);
    }
    return fresh_var;
  }

  if (size == 4) {
    encoding_clauses.push_back ({lits[start+0], lits[start+3]});

    encoding_clauses.push_back ({lits[start+1], lits[start+3]});

    encoding_clauses.push_back ({lits[start+2], lits[start+3]});

    if (add_derivation) {
    for (unsigned i = orig_size; i < encoding_clauses.size(); i++)
      encoding_derivation.push_back (encoding_clauses[i]);
    }

    return fresh_var;
  }

  // clauses with fresh var
  encoding_clauses.push_back ({fresh_var, lits[start+0]});

  encoding_clauses.push_back ({fresh_var, lits[start+1]});

  encoding_clauses.push_back ({fresh_var, lits[start+2]});

  if (add_derivation) {
    for (unsigned i = orig_size; i < encoding_clauses.size(); i++)
      encoding_derivation.push_back (encoding_clauses[i]);
    encoding_derivation.push_back ({-fresh_var, -lits[start+0],-lits[start+1],-lits[start+2]});
  }

  lits[start+2] = -fresh_var++;

  return split_full_encoding (lits, start+2, fresh_var, add_derivation);

}

// struct totalizer_node {
//   vector<int> vars;
//   vector<int> cls_idxs;
//   int first_aux;
//   int last_aux;
// };


void Internal::totalizer_branch_clauses (vector<int> left, vector<int> right, vector<int> mid, int bound, bool add_derivation) {

  int orig_size = encoding_clauses.size();

  // printf("init left %d, right  %d, mid %d\n", left.size(), right.size(), mid.size());

  // initial clauses
  for (unsigned i = 0; i < left.size() && i < bound + 1 ; i++) 
    encoding_clauses.push_back ({mid[i],-left[i]});
  for (unsigned i = 0; i < right.size() && i < bound + 1 ; i++) 
    encoding_clauses.push_back ({mid[i],-right[i]});

  // left[i] + right[j] = mid[i + j + 1]
  int sum;
  for (unsigned i = 0; i < left.size(); i++) {
    for (unsigned j = 0; j < right.size(); j++) {
      sum = i + j + 2;
      if (sum > bound + 1) continue;
      // printf("left %d, right  %d, sum %d\n", i, j,sum-1);
      encoding_clauses.push_back ({mid[sum-1],-left[i],-right[j]});
    }
  }

  if (left.size() + right.size() > (unsigned) bound) {
    // add unit enforcing bound
    encoding_clauses.push_back ({-mid[bound]});
  }

  if (add_derivation) {
    for (unsigned i = orig_size; i < encoding_clauses.size(); i++)
      encoding_derivation.push_back (encoding_clauses[i]);
  }

}

vector<int> Internal::totalizer_mid_variables (int left, int right, int bound, int &fresh_var) {
  vector<int> mid;

  int mid_size = left + right < bound + 1? left + right: bound + 1;

  for (int i = 0; i < mid_size; i++)
    mid.push_back (fresh_var++);

  return mid;
}

/*

- sort the variables based on variable score
- build branches from left to right
  
- special cases:
  1. odd # variables at start:
    - group on right
  2. odd # nodes at iteration:
    - group on right

  Probably better to just group immidiately,
  I imagine we want the more important variables 
  to be closer to the root, faster to failure
  and will propagate faster. 

*/


int Internal::totalizer_full_encoding (vector<int> lits, int bound, int fresh_var, bool add_derivation) {

  vector<vector<int>> nodes, next_nodes;

  //printf("here3\n");

  // initial nodes with problem variables
  for (unsigned i = 0; i < lits.size(); i++)
    nodes.push_back ({lits[i]});

  // balanced or true to ordering?

  // encode from left to right, bottom up
  vector<int> left, right, mid;
  while (nodes.size()) {
    //printf("here4\n");

    left = nodes[0];
    nodes.erase (nodes.begin());
    
    if (nodes.size()) {
      // two nodes, normal case
      //printf("here5\n");

      right = nodes[0];
      nodes.erase (nodes.begin());

      //printf("here7\n");

      mid = totalizer_mid_variables (left.size(), right.size(), bound, fresh_var);

      //printf("here6\n");

      totalizer_branch_clauses (left, right, mid, bound, add_derivation);

      next_nodes.push_back (mid);

    } else { // single node, attach to preivous creation

      // merge with previous node, continue
      right = left;
      left = next_nodes.back ();
      next_nodes.pop_back ();

      mid = totalizer_mid_variables (left.size(), right.size(), bound, fresh_var);

      totalizer_branch_clauses (left, right, mid, bound, add_derivation);

      next_nodes.push_back (mid);
      
    }

    if (!nodes.size ()) {
      if (next_nodes.size () == 1) break;
      nodes = next_nodes;
      next_nodes.clear ();
    }
  }


  return fresh_var;
}

int Internal::sort_by_phase (vector<int> & lits) {
  unsigned start = 0, end = lits.size()-1;

  while (start < end) {
    while (phases.best[abs(lits[start])] && start < end) start++;
    while (!phases.best[abs(lits[end])] && end > 0) end--;
    if (start < end)  
      swap (lits[start], lits[end]);
  }

  if (end < start || end == lits.size()-1) return end + 1;
  else return end;
  
}

void Internal::encode_cardinality_constraint (int cidx, bool by_score, bool add_derivation, bool only_derivation) {

  if (!only_derivation) backtrack (); // make sure we are not reusing trail (and reasons)
  
  by_score = opts.ccdclEncodingByScore;

  Clause *c = CARclauses [cidx];

  if (c->garbage) return; // do not reencode garbage constraints

  int encoding_type = 0;
  int AMO_encoding_type = 0;

  if (c->CARbound () == 1 && !only_derivation) {
    // actually a clause, let's promote it
    original.clear ();
    for (unsigned i = 0; i < c->size; i++)
      original.push_back (c->literals [i]);
    add_new_original_cardinality_clause ();
    original.clear ();

    // remove it from cardinality constraint list
    CARmark_garbage (c);
    return;
  }

  if (c->size <= 2) return;

  assert (c->CARbound () > 1);


  bool is_AMO = c->CARbound() == c->size - 1;
  int old_max_var  = max_var; // assume 1-1 between external and internal
  int fresh_var = old_max_var + 1;

  VERBOSE (0, "Encoding Cardinality Constraint %d into clauses, fresh %d",cidx, fresh_var);
  LOG (c, "Encoding Cardinality Constraint ");

  vector<int> literals;
  for (int i = 0; i < c->size; i++)
    literals.push_back (c->literals[i]);

  //printf("here1\n");
  // log_lits (literals);

  
  vector<double> *temp_tab;
  if (by_score == 1)temp_tab = &stab;
  else if (by_score == 2) temp_tab = &mptab;

  if (by_score) {

    // printf("PRE SORT\n");

    int mid = sort_by_phase (literals);

    assert (mid <= literals.size());
    // printf("Mid %d size %d\n",mid,literals.size());

    if (mid > 1)
      sort (literals.begin(), literals.begin() + mid -1, [temp_tab] (const int &a, const int &b) {return temp_tab->at(abs (a)) > temp_tab->at(abs (b));} );
    if (mid < literals.size() - 1 )
      sort (literals.begin() + mid, literals.end (), [temp_tab] (const int &a, const int &b) {return temp_tab->at(abs (a)) > temp_tab->at(abs (b));} );

    //  // sort literals based on variable score
    // sort (literals.begin(), literals.end(), [temp_tab] (const int &a, const int &b) {return temp_tab->at(abs (a)) > temp_tab->at(abs (b));} );
  }
  else 
    sort (literals.begin(), literals.end(), [] (const int &a, const int &b) {return (abs (a)) < (abs (b));} );

  // printf("c encoding cardidx %d\n",cidx);
  log_lits (literals);

  //printf("here2\n");

  if (is_AMO) {
    // handle AMO constraints
    if (AMO_encoding_type == 0) {
      fresh_var = split_full_encoding (literals, 0, fresh_var, add_derivation);
    }
  } else {
    // handle general constraints
    if (encoding_type == 0) {
      for (unsigned i = 0; i < literals.size(); i++) 
        literals[i] = -literals[i];
      fresh_var = totalizer_full_encoding (literals, literals.size() - c->CARbound (), fresh_var, add_derivation);
    }
  }

  VERBOSE (3, "Finished Generating Encoding, AMO %d", is_AMO);

  // update max variables (external/internal namings important)
  if (fresh_var-1 > old_max_var && !only_derivation)
    external->init (fresh_var-1);

  VERBOSE (3, "Finished increasing maxvar from %d to %d", old_max_var, fresh_var-1);

  // add encoding clauses to formula
  if (!only_derivation) add_encoding_clauses ();

  // remove cardinality constraint from formula
  if (!only_derivation) CARmark_garbage (c);

  // add derivation to proof
  if (add_derivation)
    add_encoding_derivation ();

  VERBOSE (3, "Finished Encoding, old max var %d, new max var %d, AMO %d", old_max_var, fresh_var-1, is_AMO);

}

void Internal::add_encoding_clauses () {

  for (auto & lits : encoding_clauses) {
    original = lits;
    // log_lits (original);
    add_new_original_cardinality_clause ();
    original.clear ();
  }

  encoding_clauses.clear ();
}

void Internal::log_lits (vector<int> lits) {
  printf("c ");
  for (auto lit: lits) printf("%d ",lit);
  printf("0\n");
}

void Internal::add_derivation_clause (vector<int> lits) {
  for (auto lit : lits) 
    encoding_derivation_file << lit << " ";
  encoding_derivation_file << "0\n"; 
}

void Internal::add_encoding_derivation () {

  for (auto & lits : encoding_derivation) {
    add_derivation_clause (lits);
  }

  encoding_derivation.clear ();
}

}