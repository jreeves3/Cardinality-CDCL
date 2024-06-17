#ifndef CHECK_SAT_H
#define CHECK_SAT_H

#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <tuple>
#include "assert.h"
#include "knf-parse.hpp"


using namespace std;

class KnfCheck : public KnfParserObserver {
public:
  
  KnfCheck () {
    acc_soft_weight = 0;
    max_weight = -1;
  }

  void partition_clauses (string solution_folder, string variable_partition_fname) ;

  void reconstruct_partitioned_solution (string solution_folder, string variable_partition_fname, string sol_fname);

  void Header(int max_var, int max_cls, int max_weight) override {

    this->max_var = max_var;
    this->max_cls = max_cls;
    this->max_weight = max_weight;

  }

  void Clause(vector<int>& lits, double weight, string s_weight) override {

    if (lits.size() == 0) {
      cout << "empty lits\n";
      cout << "Line number " << cardinality_constraints.size() + clauses.size() << endl;
      return;
    }

    vector<int> temp = lits;

    clauses.push_back(temp);
    clause_weights.push_back (weight);
    clause_s_weights.push_back (s_weight);
    if (has_weight ())
      {if (stoi (s_weight) != max_weight ) acc_soft_weight += stoi (s_weight);}

  }

  void CardinalityConstraint(vector<int>& lits, int bound, double weight, string s_weight, int guard) override {

    vector<int> temp = lits;
    int tempB = bound;

    if (lits.size() == 0) {
      cout << "empty lits\n";
      cout << "Line number " << cardinality_constraints.size() + clauses.size() << endl;
      return;
    }

    if (bound == 0) { // trivially satisfied constraint??
      cout <<"trivially satisfied consrtaint with bound 0\n";
      cout << "Line number " << cardinality_constraints.size() + clauses.size() << endl;
      return;
    }

    if (bound == 1) { // keep clauses separate
      Clause (lits, weight, s_weight);
    } else {
      cardinality_constraints.push_back(make_tuple(temp, bound));
      card_weights.push_back (weight);
      card_s_weights.push_back (s_weight);
      card_guards.push_back (guard);
      
      if (has_weight ())
      {if (stoi (s_weight) != max_weight ) acc_soft_weight += stoi (s_weight);}
    }

  }


  void Comment(const string& comment) override {;}

  /*
  
    Count number of satisifed/falsified clauses and cardinality constraints

  */
  void checkSat () {

    cardSat = cardUnsat = clauseSat = clauseUnsat = 0;

    for (auto lits : clauses) {
      int sat = 0;
      for (auto lit : lits) {
        if (get_value(abs(lit)) == abs(lit)/lit) sat++;
      }
      if (sat >= 1) {
        clauseSat++;
      } else {
        clauseUnsat++;
      }
    }

    for (unsigned i = 0; i < cardinality_constraints.size () ; i++) {
      auto tpl = cardinality_constraints [i];
      if (card_guards [i] && get_value(abs(card_guards [i])) == abs(card_guards [i])/card_guards [i]) {
        cardSat++;
        continue;
      }
      int sat = 0;
      for (auto lit : get<0>(tpl)) {
        if (get_value(abs(lit)) == abs(lit)/lit) sat++;
      }
      if (sat >= get<1>(tpl)) {
        cardSat++;
      } else {
        cardUnsat++;
        write_card (i);
      }
    }

  }

  void write_clause (int cidx) {
    for (auto lit : clauses[cidx]) cout << lit << " ";
    cout << 0 << endl;
  }

  void write_card (int cidx) {
    for (auto lit : get<0> (cardinality_constraints[cidx])) cout << lit << " ";
    cout << 0 << endl;
  }

  /*
  
    Count number of satisifed/falsified clauses and cardinality constraints

    Differentiate between soft and hard constraints

    Count total weight
    
  */
  void checkMaxSat () {

    vector<int> lits;
    double weight;

    hard_sat = hard_unsat = soft_sat = soft_unsat = 0;
    card_hard_sat = card_hard_unsat = card_soft_sat = card_soft_unsat = 0;

    total_soft_unsat_weight = total_soft_sat_weight = 0.0;
    card_total_soft_unsat_weight = card_total_soft_sat_weight = 0.0;

    for (int i = 0; i < clauses.size(); i++) {
      lits = clauses[i];
      int sat = 0;
      weight = clause_weights[i];
      for (auto lit : lits) {
        if (get_value(abs(lit)) == abs(lit)/lit) sat++;
      }
      if (sat >= 1) {
        if (weight == max_weight) {
          hard_sat++;
        } else {
          soft_sat++;
          total_soft_sat_weight += weight;
        }
      } else {
        if (weight == max_weight) {
          write_clause (i);
          hard_unsat++;
        } else {
          soft_unsat++;
          total_soft_unsat_weight += weight;
        }
      }
    }
    

    for (int i = 0; i < cardinality_constraints.size(); i++) {
      int sat = 0;
      auto tpl = cardinality_constraints[i];
      weight = card_weights[i];
      for (auto lit : get<0>(tpl)) {
        if (get_value(abs(lit)) == abs(lit)/lit) sat++;
      }
      if (sat >= get<1>(tpl)) {
        if (weight == max_weight) {
          card_hard_sat++;
        } else {
          card_soft_sat++;
          card_total_soft_sat_weight += weight; // possibly calculate this differently
        }
      } else {
        if (weight == max_weight) {
          write_card (i);
          card_hard_unsat++;
        } else {
          card_soft_unsat++;
          card_total_soft_unsat_weight += weight; // possibly calculate this differently
        }
      }
    }

  }

  void printResult () {

    if (has_weight ()) {
      if (card_hard_sat + card_hard_unsat + card_soft_sat + card_soft_unsat != cardinality_constraints.size()) {
        cout << "ERROR counting error on cardinality constraints" << endl;
        exit(1);
      }

      if (hard_sat + hard_unsat + soft_sat + soft_unsat != clauses.size()) {
        cout << "ERROR counting error on clauses" << endl;
        exit(1);
      }

      int card_nunsat = card_hard_unsat + card_soft_unsat;
      int nunsat = hard_unsat + soft_unsat;

      if ( card_nunsat + nunsat == 0) {
        cout << "c VERIFIED SATISFIABLE" << endl;
        cout << "c cardSAT: " << cardSat << endl;
        cout << "c cardUNSAT: " << cardUnsat << endl;
        cout << "c clauseSAT: " << clauseSat << endl;
        cout << "c clauseUNSAT: " << clauseUnsat << endl;
      }
      else {
        if (card_hard_unsat + hard_unsat > 0) {
          cout << "c NOT SATISFYING hard constraints" << endl;
          cout << "c clauses hard_unsat " << hard_unsat << " hard sat " << hard_sat << endl;
          cout << "c card hard_unsat " << card_hard_unsat << " hard sat " << card_hard_sat << endl;
        } else cout << "c SATISFYING hard constraints" << endl;
        cout << "c count clauses soft sat " << soft_sat << " soft unsat " << soft_unsat << endl;
        cout << "c weights clauses soft sat " << total_soft_sat_weight << " soft unsat " << total_soft_unsat_weight << endl;
        cout << "c count card soft sat " << card_soft_sat << " soft unsat " << card_soft_unsat << endl;
        cout << "c weights card soft sat " << card_total_soft_sat_weight << " soft unsat " << card_total_soft_unsat_weight << endl;

        cout << "c count total soft sat " << soft_sat + card_soft_sat << " soft unsat " << soft_unsat + card_soft_unsat << endl;
        cout << "c weights total soft sat " << total_soft_sat_weight + card_total_soft_sat_weight  << " soft unsat " << total_soft_unsat_weight + card_total_soft_unsat_weight << endl;
      }

    } else {
      if (cardUnsat+cardSat != cardinality_constraints.size()) {
        cout << "ERROR cardSAT+cardUNSAT not equal to size" << endl;
        exit(1);
      }

      if (clauseUnsat+clauseSat != clauses.size()) {
        cout << "ERROR clauseSAT+clauseUNSAT not equal to size" << endl;
        exit(1);
      }

      if (cardUnsat+clauseUnsat == 0) {
        cout << "c VERIFIED SATISFIABLE" << endl;
        cout << "c cardSAT: " << cardSat << endl;
        cout << "c cardUNSAT: " << cardUnsat << endl;
        cout << "c clauseSAT: " << clauseSat << endl;
        cout << "c clauseUNSAT: " << clauseUnsat << endl;
      }
      else {
        cout << "c NOT satisfying assignment" << endl;
        cout << "c cardSAT: " << cardSat << endl;
        cout << "c cardUNSAT: " << cardUnsat << endl;
        cout << "c clauseSAT: " << clauseSat << endl;
        cout << "c clauseUNSAT: " << clauseUnsat << endl;
      }
    }
    
  }


  bool parseAssignment (string assignment_path, Input_Type input_type) {

    fstream assignment_file(assignment_path, ios_base::in);

    if (!assignment_file) return false;

    string c;
    int lit;

    cout << "Parsing assignment\n";

    // initialize assignment
    for (int i = 0; i < max_var+1; i++) assignment.push_back(0);

    if (input_type == CAI) {
      int cnt = 0;
      while (assignment_file >> c) {
        if (c == "v" || c == "i") continue;;
        lit = stoi (c);
        assignment[cnt++] = lit;
      }
    } else if (input_type == LSECNF) {
      int cnt = 0;
      int first = 1;
      while (assignment_file >> c) {
        if (c == "v" || c == "i") continue;;
        lit = stoi (c);
        if (first) {
          first = 0;
          continue;
        }
        assignment[cnt++] = lit;
      }
    } else {

    while (assignment_file >> c) {
        if (c == "v" || c == "i") continue;
        lit = stoi (c);
        if (abs(lit) > max_var) {
          continue;
          // cout << "ERROR variable in assignment " << abs(lit) << " greater than max_var " << max_var << endl;
          // exit(1);
        } else {
        
          if (assignment[abs(lit)]) {
            cout << "ERROR variable appears twice in assignment" << endl;
            exit(1);
          }

          if (!lit) continue;

          assignment[abs(lit)] = lit/(abs(lit));
        }
    }

    for (int i = 0; i < max_var+1; i++) {
      if (!assignment[i]) assignment[i] = -1;
    }
    }

    return true;
 
  }

  void writeKnf (string out_path) {

    ofstream out_file(out_path);

    cout << "writing to " << out_path << endl;

    out_file << "c converted file format" << endl;

    int new_cls = cardinality_constraints.size() + clauses.size();

    cout << "Old header with " << max_cls << " constraints, new header with " << new_cls << " constraints\n";

    // write header
    if (has_weight()) out_file << "p wknf " << max_var << " " << new_cls << " " << max_weight << endl;
    else out_file << "p knf " << max_var << " " << new_cls << endl;

    // write clauses
    for (int i = 0; i < clauses.size(); i++) {
      if (has_weight()) out_file << clause_s_weights[i] << " ";
      for (auto lit : clauses[i]) out_file << lit << " ";
      out_file << "0" << endl;
    }

    // write cardinality constraints
    for (int i = 0; i < cardinality_constraints.size(); i++) {
      if (has_weight()) out_file << card_s_weights[i] << " ";
      auto tpl = cardinality_constraints[i];
      out_file << "k " << get<1>(tpl) << " ";
      for (auto lit : get<0>(tpl)) out_file << lit << " ";
      out_file << "0" << endl;
    }

    out_file.close ();

  }

  void writeCai (string out_path) {

    ofstream out_file(out_path);

    cout << "writing to " << out_path << endl;

    // out_file << "c converted file format" << endl;

    int new_cls = cardinality_constraints.size() + clauses.size();

    cout << "Old header with " << max_cls << " constraints, new header with " << new_cls << " constraints\n";

    if (!has_weight ()) {
      cout << "Must write formulas with weight to Cai output\n";
      exit (1);
    }

    // write header
    out_file << "p wcnf " << max_var << " " << new_cls << " " << acc_soft_weight * 10 << endl;

    // write clauses
    for (int i = 0; i < clauses.size(); i++) {
      if (stoi (clause_s_weights[i]) != max_weight) continue;
      if (stoi (clause_s_weights[i]) == max_weight) {
        out_file << acc_soft_weight * 10 << " 1 ";
      } else
        out_file << clause_s_weights[i] << " 1 ";

      for (auto lit : clauses[i]) out_file << lit << " ";
      out_file << "0" << endl;
    }

    // write cardinality constraints
    for (int i = 0; i < cardinality_constraints.size(); i++) {
      if (stoi (card_s_weights[i]) != max_weight) continue;
      if (stoi (card_s_weights[i]) == max_weight) {
        out_file << acc_soft_weight * 10 << " ";
      } else
        out_file << card_s_weights[i] << " ";

      auto tpl = cardinality_constraints[i];
      out_file << get<1>(tpl) << " ";
      for (auto lit : get<0>(tpl)) out_file << lit << " ";
      out_file << "0" << endl;
    }

    // write clauses
    for (int i = 0; i < clauses.size(); i++) {
      if (stoi (clause_s_weights[i]) == max_weight) continue;
      if (stoi (clause_s_weights[i]) == max_weight) {
        out_file << acc_soft_weight * 10 << " 1 ";
      } else
        out_file << clause_s_weights[i] << " 1 ";

      for (auto lit : clauses[i]) out_file << lit << " ";
      out_file << "0" << endl;
    }

    // write cardinality constraints
    for (int i = 0; i < cardinality_constraints.size(); i++) {
      if (stoi (card_s_weights[i]) == max_weight) continue;
      if (stoi (card_s_weights[i]) == max_weight) {
        out_file << acc_soft_weight * 10 << " ";
      } else
        out_file << card_s_weights[i] << " ";

      auto tpl = cardinality_constraints[i];
      out_file << get<1>(tpl) << " ";
      for (auto lit : get<0>(tpl)) out_file << lit << " ";
      out_file << "0" << endl;
    }

    out_file.close ();

  }

  bool has_weight () {return max_weight != -1;}

private:

  int get_value (int var) {
    if (var > max_var) {
      cout << "ERROR index " << var << " greater than max_var" << endl;
      exit (1);
    }
    return assignment[var];
  }

  vector<vector<int>> clauses;
  vector<tuple<vector<int>,int>> cardinality_constraints;
  vector<int> card_guards;
  vector<int> clause_weights, card_weights;
  vector<string> clause_s_weights, card_s_weights;

  vector<int> assignment;

  int max_var, max_cls, max_weight, cardSat,cardUnsat,clauseSat,clauseUnsat;

  int acc_soft_weight;

  int total_soft_unsat_weight, total_soft_sat_weight;
  int card_total_soft_unsat_weight, card_total_soft_sat_weight;

  int hard_sat, hard_unsat, soft_sat, soft_unsat;
  int card_hard_sat, card_hard_unsat, card_soft_sat, card_soft_unsat;

};

#endif