#ifndef CNF_PARTITION_H
#define CNF_PARTITION_H

#include <iostream>
#include <string>
#include <vector>
#include <algorithm>
#include <unordered_set>
#include <fstream>
#include "stdlib.h"

using namespace std;


/*

  Finds connected components of a CNF formula.

  Outputs:
  - Formula for each connected component
  - Text file containing variable partitions
    nPartitions, maxVar, 
    variables
    0 // new partition
    variables
    ...

*/
void KnfCheck::partition_clauses (string formula_folder, string variable_partition_fname) {

  unordered_set<int> *e_graph;
  e_graph = new unordered_set<int>[this->max_var+1];

  cout << "Making graph" << endl;
  for (int i = 0; i < clauses.size (); i++) {
    // if (clause_weights[i] == max_weight) continue;
    vector<int> lits = clauses[i];
    for (auto lit1 : lits) {
      for (auto lit2 : lits) { // could do MIN (), MAX ()
        e_graph[abs(lit1)].insert (abs(lit2));
        e_graph[abs(lit2)].insert (abs(lit1));
      }
    }
  }

  for (int i = 0; i < cardinality_constraints.size(); i++) {
    // if (card_weights[i] == max_weight) continue;
    auto tpl = cardinality_constraints[i];
    for (auto lit1 : get<0>(tpl)) {
      for (auto lit2 : get<0>(tpl)) { // could do MIN (), MAX ()
        e_graph[abs(lit1)].insert (abs(lit2));
        e_graph[abs(lit2)].insert (abs(lit1));
      }
    }
  }

  int *variable_partitions;
  
  variable_partitions = new int[this->max_var+1];

  for (int i = 0; i < this->max_var+1; i++) {
    variable_partitions[i] = -1;
  }

  cout << "Starting BFS" << endl;

  int Par = 0, last_var_start = 1;
  vector<int> frontier;

  while (last_var_start <= this->max_var) {

    frontier.push_back (last_var_start);

    while (!frontier.empty()) { // BFS
      int var = frontier.back();
      frontier.pop_back ();

      if (var <= 0 || var > this->max_var) {
        cout << "Var " << var << " out of bounds" << endl;
        exit (1);
      }

      if (variable_partitions[var] >= 0) continue;

      variable_partitions[var] = Par;

      for (auto neigh = e_graph [var].begin (); neigh != e_graph [var].end (); ++neigh) {
        if (*neigh <= 0 || *neigh > this->max_var) {
          cout << "Var " << *neigh << " out of bounds" << endl;
          exit (1);
        }
        
        if (variable_partitions[*neigh] >= 0 || variable_partitions[*neigh] == -2)
          continue;
        frontier.push_back (*neigh);
        variable_partitions[*neigh] = -2; // on the frontier already
      }
    }

    // get starting variable for next partition
    for (; last_var_start < this->max_var+1; last_var_start++) {
      if (variable_partitions[last_var_start] == -1)
        break;
    }
    Par++;
    cout << "End " << Par << " Partition" << endl;
  }

  int part_soft_cnt[Par];
  int diff, prev, curr;
  for (int i = 0; i < Par; i++) part_soft_cnt[i] = 0;
  cout << "Finding partition soft count" << endl;
  for (int i = 0; i < clauses.size (); i++) {
    if (clause_weights[i] == max_weight) continue;
    vector<int> lits = clauses[i];
    diff = 0;
    curr = prev = variable_partitions [abs(lits[0])];
    part_soft_cnt [ curr ]++;
    for (auto lit1 : lits) {
      curr = variable_partitions [abs(lit1)];
      if (prev != curr) diff = 1;
      prev = curr;
    }
    if (diff) {
      cout << "ERROR" <<endl;
    }
  }


  // Code for finding differences between partitions

  // int shared_hard_clauses[Par];
  // for (int i = 0; i < Par; i++) shared_hard_clauses[i] = 0;
  
  // unordered_set<int> lit_parts;

  // cout << "Finding differences between partitions" << endl;
  // for (int i = 0; i < clauses.size (); i++) {
  //   if (clause_weights[i] != max_weight) continue;
  //   vector<int> lits = clauses[i];
  //   diff = 0;
  //   lit_parts.clear ();
  //   curr = prev = variable_partitions [abs(lits[0])];
  //   for (auto lit1 : lits) {
  //     curr = variable_partitions [abs(lit1)];
  //     if (prev != curr) diff = 1;
  //     prev = curr;
  //     lit_parts.insert (curr);
  //   }
  //   if (diff) {
  //     for (auto it = lit_parts.begin (); it != lit_parts.end (); it++ ) {
  //       shared_hard_clauses [*it]++;
  //     }
  //   }
  // }

  // cout << "onto card constriants " << endl;
  // for (int i = 0; i < cardinality_constraints.size(); i++) {
  //   if (card_weights[i] != max_weight) continue;
  //   auto tpl = cardinality_constraints[i];
  //   vector<int> lits = get<0> (tpl);
  //   diff = 0;
  //   lit_parts.clear ();
  //   int in_big = 0;
  //   int in_big_first = -1;
  //   curr = prev = variable_partitions [abs(lits[0])];
  //   for (auto lit1 : lits) {
  //     curr = variable_partitions [abs(lit1)];
  //     if (curr == 0 || curr == 1 || curr == 6) {
  //       if (in_big_first >= 0) {
  //         if (in_big_first != curr)
  //           in_big = 1;
  //       } else in_big_first = curr;
  //     }
  //     if (prev != curr) diff = 1;
  //     prev = curr;
  //     lit_parts.insert (curr);
  //   }
  //   if (diff) {
  //     for (auto it = lit_parts.begin (); it != lit_parts.end (); it++ ) {
  //       // if (in_big)
  //         shared_hard_clauses [*it]++;
  //     }
  //   }
  // }

  // //check difference between partitions
  // for (int i = 0; i < Par; i++) {
  //   cout << "Partition " << i << " has difference " << shared_hard_clauses[i] << " with soft count " << part_soft_cnt[i] << endl;
  // }

  cout << "Writing " << Par << " Partitions" << endl;

  // write the partition file
  ofstream partition_file(variable_partition_fname);
  partition_file << Par << " " << this->max_var << endl;
  for (int i = 0; i < Par; i++) {
    for (int v = 0 ; v < this->max_var+1; v++) {
      if (variable_partitions[v] == i) {
        partition_file << v << endl;
      }
    }
    if (i < Par-1) partition_file << 0 << endl;
  }
  partition_file.close();

  int cls_size = this->clauses.size();
  int card_size = this->cardinality_constraints.size();
  int clause_in[cls_size];
  int card_in[card_size];

  // write the new formulas
    // one pass to get clause count for header
  for (int P = 0; P < Par; P++) {
    
    // clauses
    for (int i = 0; i < cls_size; i ++) clause_in[i] = 0;
    int nCls = 0;
    for (int i = 0; i < cls_size; i ++) {
      for (auto lit: clauses[i]) {
        if (variable_partitions[abs(lit)] == P) {
          if (!clause_in[i]) nCls++;
          clause_in[i] = 1;
          break;
        }
      }
    }

    // cardinality constraints
    for (int i = 0; i < card_size; i ++) card_in[i] = 0;
    int nCard = 0;
    for (int i = 0; i < card_size; i ++) {
      auto tpl = cardinality_constraints[i];
      for (auto lit: get<0>(tpl)) {
        if (variable_partitions[abs(lit)] == P) {
          if (!card_in[i]) nCard++;
          card_in[i] = 1;
          break;
        }
      }
    }

    ofstream formula_file(formula_folder + to_string (P) + ".wknf");
    // write header
    formula_file << "p wknf " << this->max_var << " " << nCls + nCard << " " << 1000 << endl;

    // write clauses
    for (int i = 0; i < cls_size; i ++) {
      if (clause_in[i]) {
        formula_file << clause_weights[i] << " ";
        for (auto lit: clauses[i]) {
          formula_file << lit << " ";
        }
        formula_file << 0 << endl;
      }
    }

    // write cconstraints
    for (int i = 0; i < card_size; i ++) {
      if (card_in[i]) {
        auto tpl = cardinality_constraints[i];
        formula_file << card_weights[i] << " k ";
        formula_file << get<1>(tpl) << " ";
        for (auto lit: get<0>(tpl)) {
          formula_file << lit << " ";
        }
        formula_file << 0 << endl;
      }
    }

    formula_file.close();
    cout << "Partition " << P << " written" << endl;

  }        

}
 

/*

  Combines the solutions for multiple patitioned formulas

  Input:
    - set of solutions (1.sol ... n.sol)
    - variable partitions file

  Output:
    - combined solution for original formula to standard out
    
*/
void KnfCheck::reconstruct_partitioned_solution (string solution_folder, string variable_partition_fname, string sol_fname) {

  int var, nPartitions, maxVar;

  ifstream partition_file(variable_partition_fname);

  partition_file >> nPartitions;
  partition_file >> maxVar;

  int variable_partitions[maxVar+1];

  for (int i = 0; i < maxVar; i++) {
    variable_partitions[i] = -1;
  }

  // cout << "c Variables " << maxVar << " Partitions " << nPartitions << endl;

  // find which partition each variable is in
  int Par = 0;
  while (partition_file >> var) {
    if (var == 0) // next partition
      Par++;
    else 
      variable_partitions[var] = Par;
  }

  // parse the solutions
  ofstream sol_file(sol_fname);


  int lit;
  string c;
  int brkCnt = 0;
  for (int i = 0; i < nPartitions; i++) {
    // cout << solution_folder + to_string (i) + ".sol" << endl;
    ifstream solution_file(solution_folder + to_string (i) + ".sol");
    while (solution_file >> c) {
      if (c == "v") continue;
      lit = stoi (c);
      if (variable_partitions[abs(lit)] == i) {
         // lit in this partition
        sol_file << lit << " ";
        brkCnt++;
        if (brkCnt == 8) {sol_file << endl; brkCnt = 0;}
      }
    }
  }

}



#endif