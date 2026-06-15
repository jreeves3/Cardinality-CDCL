#ifndef MAIN_H
#define MAIN_H

#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <tuple>
#include <algorithm>
#include <set>
#include "assert.h"
#include "knf-parse.hpp"


using namespace std;

class KnfProx : public KnfParserObserver {
public:

  vector<vector<int>> clauses;
  vector<tuple<vector<int>,int>> cardinality_constraints;
  vector<vector<int>>  occ_list;
  vector<int>  occ_count;
  set<int>  k_variables;
  vector<int>  processed;
  vector<double> scores;
  vector<int> score_heap;
  vector<vector<int>> AMO_constraints;

  vector<int> fake_heap ;

  vector<vector<int>>  pos_occ_list, neg_occ_list;

  vector<int> var_ord_map;
  
  KnfProx () {
    max_weight = -1;
  }

  // Parse KNF header
  void Header(int max_var, int max_cls, int max_weight) override {

    this->max_var = max_var;
    this->max_cls = max_cls;
    this->max_weight = max_weight;

    occ_count.resize (max_var+1);
    processed.resize (max_var+1);  

    pos_occ_list.resize (max_var+1);
    neg_occ_list.resize (max_var+1);

    for (int i = 0; i <= max_var; i++) var_ord_map.push_back(i);

  }

  void print_ordered_knf () {
    int nVars = max_var;
    int nCls = clauses.size() + cardinality_constraints.size();
    cout << "p cnf " << nVars << " " << nCls << endl;
    for (auto card: cardinality_constraints) {
      // sort lits by variable order map
      vector<int> sorted_lits = get<0>(card);
      sort (sorted_lits.begin(), sorted_lits.end(), [&](int a, int b) {return var_ord_map[abs(a)] < var_ord_map[abs(b)];});
      cout << "k " << get<1>(card) << " ";
      for (auto lit: sorted_lits) cout << lit << " ";
      cout << "0" << endl;
    }
    for (auto cls: clauses) {
      for (auto lit: cls) cout << lit << " ";
      cout << "0" << endl;
    }
  }

  // Parse Clause
  void Clause(vector<int>& lits, double weight, string s_weight) override {

    if (lits.size() == 0) {
      cout << "empty lits\n";
      cout << "Line number " << cardinality_constraints.size() + clauses.size() << endl;
      return;
    }

    vector<int> temp = lits;

    clauses.push_back(temp);

    for (auto lit: lits) {
      if (lit > 0) pos_occ_list [abs(lit)].push_back (clauses.size()-1);
      else neg_occ_list [abs(lit)].push_back (clauses.size()-1);

      occ_count [abs(lit)]++;
    }

  }

  // Parse Cardinality constraint
  void CardinalityConstraint(vector<int>& lits, int bound, double weight, string s_weight, int guard) override {

    vector<int> temp = lits;
    int tempB = bound;

    if (lits.size() == 0) {
      cout << "empty lits\n";
      cout << "Line number " << cardinality_constraints.size() + clauses.size() << endl;
      return;
    }

    if (bound == 1) { // keep clauses separate
      Clause (lits, weight, s_weight);
    } else {
      cardinality_constraints.push_back(make_tuple(temp, bound));
      if (bound == lits.size() -1) {
        AMOConstraint (lits, bound, weight, s_weight, guard);
      }
    }

  }

  // Prase AMO constraint
  void AMOConstraint(vector<int>& lits, int bound, double weight, string s_weight, int guard) override {

    vector<int> temp = lits;
    int tempB = bound;

    // only count AMO constraints with more than 5 literals
    if (bound <= 4) return;
    
    AMO_constraints.push_back(temp);

    for (auto lit: lits) {
      if (lit > 0) pos_occ_list [abs(lit)].push_back (-(AMO_constraints.size()-1));
      else neg_occ_list [abs(lit)].push_back (-(AMO_constraints.size()-1));
    }


  }

  void Comment(const string& comment) override {;}

  // Get next unprocessed variable by occurrence count
  int get_variable_by_occur () {
    int best_k_occ = 0;
    int best_k = 0;
    for (auto var: k_variables) {
      if (processed[var]) continue;
      if (occ_count[var] > best_k_occ) {
        best_k_occ = occ_count[var];
        best_k = var;
      }
    }
    return best_k;
  }

  // Get next unprocessed variable by max Score
  //   if no unprocessed variable has score > 0, 
  //      select next variable by most occurrences
  int get_next_variable () {
    int res = 0;
    if (fake_heap.size() == 0) {

      // most occurrent variable
      return get_variable_by_occur ();
    }
    else {

      // max score variable
      auto max_it = max_element(fake_heap.begin(), fake_heap.end(), [&](int a, int b) {return scores[a] < scores[b];});
      res = *max_it;

      fake_heap.erase(max_it);

      return res;
    }
  }

  /*

    Perform the proximity algorithm
  
  */
  void get_proximity (double bias_change) {

    // list of variables in cardinality constraints that 
    // must be processed (put into the ordering)
    // all parsed cardinality cosntraints: 
    for (auto card: cardinality_constraints) {
      for (auto lit: get<0>(card))
        k_variables.insert (abs(lit));
    }

    // get variable to start proximity computation
    int first_variable = get_variable_by_occur ();

    score_heap = {first_variable};

    scores.resize (max_var+1);

    int nprocessed = 0;
    int kCount = k_variables.size();
    double processed_order_bias = 0.000001;

    // Additional arguments not used in the AAAI paper
    bias_change = 0.000001;
    double iteration_bias = 0.000001;

    vector<int> ordered_variables;

    fake_heap = {first_variable};

    while (nprocessed < max_var) {

      // 1. Get next variable
      int next_variable = get_next_variable ();

      // 2. Add to ordering
      ordered_variables.push_back(next_variable);

      processed[next_variable] = 2; 
      nprocessed++;

      // 5. stop once all k_variables have been processed
      if (k_variables.find(next_variable) != k_variables.end()) {
        kCount--;
        if (kCount <= 0)
          break;
      }

      iteration_bias += bias_change;

      set<int> new_vars;
      set<int> changed_vars;
      set<int> AMO_vars;

      int switch_occ = false;

      // loop over positive occurences then negative occurences
      while (true) {
        
        vector<int> *occ_list_p;
        if (switch_occ) occ_list_p = &neg_occ_list[next_variable];
        else occ_list_p = &pos_occ_list[next_variable];

        for (auto cls: (*occ_list_p)) {

          // Steps 3,4: loop over all AMO constraints and clauses, 
          //            performing score updates

          vector<int> lits;
          double cls_score ;
          if (cls < 0) { // Step 3. AMO constraint
            cls = -cls;
            lits = AMO_constraints[cls];
            cls_score = (lits.size()) * lits.size(); // AMO score is len(K)^2
          } else { // Step 4. Clause
            lits = clauses[cls];
            if (lits.size() == 2) {
              cls_score = (lits.size()) * lits.size(); // binary clause score is len(2)^2=4

            }
            else
              cls_score = 1.0/(lits.size()); // clause score is 1/len(C)
          }

          // Update the scores of unprocessed variabels touched by the constraints
          for (auto lit: lits) {
            if (processed[abs(lit)] == 2) continue;

            if (lits.size() == 2) AMO_vars.insert(abs(lit));
            if (processed[abs(lit)] == 0){
              // new variable is seen, add a small bias to favor earlier variables
              // Mentioned in AAAI paper as tiebreaking.
              processed[abs(lit)] = 1;

              fake_heap.push_back(abs(lit));

              // tie breaking favors older variables
              scores[abs(lit)] += cls_score- processed_order_bias;

              processed_order_bias += .000001;

            } else scores[abs(lit)] += cls_score;
          }
        }
        if (switch_occ) break;
        switch_occ = true;
      }
    }


    // print ordering
    cout << "c Proximity ordering: " ;
    for (int i = 0; i < ordered_variables.size(); i++) {
      cout << ordered_variables[i] << " ";
    } cout << endl;

    for (int i = 0; i < ordered_variables.size(); i++) {
      var_ord_map[ordered_variables[i]] = i;
    }

  }

private:

  int max_var, max_cls, max_weight;

};

#endif