/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
========================================================================*/

/*
 Enable generation of a BDD from a set of clauses
 where some variables are data variables and others are encoding variables
 Resulting BDD is only over data variables

 Assume that variables are numbered from 1 to nvar,
 with the first dvar of these being data variables
*/

#pragma once

#include <vector>
#include <unordered_set>
#include <unordered_map>

#include "tbdd.h"

using namespace std;

namespace trustbdd {

class Term {
private:
  int term_id;
  tbdd tfun;
  int node_count;
  bool is_active;

public:
  Term (tbdd t);
  ~Term();

  // Returns number of dead nodes generated
  int deactivate();

  bool active() { return is_active; }

  tbdd &get_fun() { return tfun; }

  bdd get_root() { return tfun.get_root(); }

  int get_term_id() { return term_id; }

  int get_node_count() { return node_count; }


};

  // Class for constructing BDD representation of set of clauses
  // formed by conjuncting variables and quantifying out encoding variables
  
  // Variables numbered from 1 to nvar
  // Data variables numbered from 1 to ndata

class TermSet {

private:
  
  int nvar;
  int ndata;

  // Vector of terms, indexed as t-1
  vector<Term *> terms;

  // Root variable
  bdd root;

  int verblevel;
  // Garbage collection monitors
  int total_count;
  int dead_count;
  // Statistics
  int and_count;
  int quant_count;
  int max_bdd;

public:
  TermSet(int nvar, int ndata, ilist var_order, int vlevel);
  ~TermSet();

  // Add clause.  Literals must be numbered according to local conventions.  Return Term ID
  int add_clause(ilist literals);
  int add_clause(int *ldata, int len);

  // Reduce via bucket elimination.  Return true if successful
  bool bucket_reduce();

  // Get root of resulting BDD
  bdd get_root() { return root; }

  void show_statistics();

  // Decode generated BDD into representation of cardinality constraint
  // If successful, fills in list of data literals and lower & upper bound parameters
  bool cardinality_converter(vector<int> &lits, int *lower, int *upper);


private:
  // Largest BDD allowed
  long int bdd_size_limit();

  Term *get_term(int tid);

  int add(tbdd t);

  void check_gc();

  int conjunct(int tid1, int tid2);

  int equantify(int tid, int var);

  // Find level of uppermost encoding variable
  // or 0 if independent of encoding variables
  int find_bucket_level(int tid);




};

// For representing edges in graph
struct edge {
  int node1;
  int node2;
  float weight;
};


// Class to find a good ordering of variables
// based on graph structure induced by clauses
class Ordering {

private:
  int verblevel;
  // Number of data and encoding variables.
  // Assume data variables between 1 and ndata
  // encoding variables between ndata+1 and nvar
  int ndata, nvar;
  // Undirected graph with vertices = encoding variables
  // Edge if occur in same clause
  // Represent by list of edges 
  vector<edge> edge_list;
  // + mapping from each vertex to its set of edges
  // Represent edge by index into edge_list
  vector<unordered_set<int>> encoded_edge;
  // For each encoding variable, set of data variables that occur in same clause
  // Indexed by v-ndata-1
  vector<unordered_set<int>> data_neighbor;
  // For each data variable, set of encoding variables that occur in same clause
  // Indexed by v-1
  vector<unordered_set<int>> encoding_neighbor;
  // Mapping from pair of encoding variables to edge index
  // to ensure that edge is unique
  unordered_map<int,int> unique_edge;
  

public:
  Ordering(int nvar, int ndata, int verblevel);
  void add_clause(int *ldata, int len);

  // Construct an suitable ordering of all of the variables
  ilist generate_ordering(unsigned seed);

private:
  // Helper routines
  void add_weights();
  float shortest_paths(int vsource, vector <int> &visited, vector <int> &length, bool all_nodes);
  void order_encoded(vector<int> &evar);
};


} // trustbdd
