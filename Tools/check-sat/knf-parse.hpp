#ifndef KNF_PARSE_H
#define KNF_PARSE_H

#include <iostream>
#include <string>
#include <vector>
#include <algorithm>
#include <unordered_set>
#include <fstream>
#include <math.h>
/*

Parses a KNF formula

TODO: extend to a general pseudo-Boolean formula

*/



using namespace std;

// type 
enum Input_Type {UNKNOWN,CNF,KNF,WCNF,WKNF,WCARD,CAI,LSECNF} ;


class KnfParserObserver {
public:
  virtual void Header(int max_var, int max_cls, int max_weight) {};
  virtual void Clause(vector<int>& clause, double weight, string s_weight) {};
  virtual void CardinalityConstraint(vector<int>& clause, int bound, double weight, string s_weight, int guard) {};
  virtual void Comment(const string& comment) {};
};

class KnfParser {
public:

  virtual void Parse(string knf_path, Input_Type input_type) = 0;

  void AddObserver(KnfParserObserver* observer) {
    observers_.emplace_back(observer);
  }

protected:

  vector<KnfParserObserver*> observers_;
};

class PlainTextKnfParser : public KnfParser {
public:
  void Parse(string knf_path, Input_Type input_type) override {
    FILE* file = fopen(knf_path.c_str(), "r");
    if (!file) throw "File " + knf_path + " cannot be opened.";
    int c = getc_unlocked(file);
    SkipWhitespace(file, c);
    int statement_type = 0;
    vector<int> clause;
    int idx;
    int bound, max_var, max_cls, max_weight = -1;
    int guard = 0;
    bool header;
    int ncls = 0;
    Input_Type parsed_type;
    string s_weight;

    cout << "start parsing" << endl;

    while (c != EOF) {

      if(c == 'c') { // comment
        auto comment = ParseLine(file, c);
        for(auto observer : observers_) {
          observer->Comment(comment);
        }
        continue;
      }

      if(c == 'p') { // parse header : p knf <var> <cls>

        c = getc_unlocked(file); // skip 'p'
        SkipWhitespace(file, c);

        if (DetermineHeader (file, c, max_var, max_cls, max_weight, parsed_type)) {
          header = true;
        }

        break;
      }

    }

    if (!header) {
      cout << "ERROR no header parsed" << endl;
      exit(1);
    } 

    cout << "c Header parsed with " << max_var << " variables " << max_cls << " clauses" ;
    if (max_weight >= 0) cout << " and " << max_weight << " hard weight";
    cout << endl;

    if (input_type != UNKNOWN && input_type != CAI && parsed_type != input_type) {
      cout << "ERROR input type " << input_type << " does not match parsed type " << parsed_type << endl;
      exit(1);
    }

    if (input_type == UNKNOWN) input_type = parsed_type;


    bool weight_check = false;
    if (input_type == WCNF || input_type == WKNF || input_type == CAI || input_type == WCARD) {
      assert (max_weight >= 0);
      weight_check = true;
    }

    for(auto observer : observers_) {
          observer->Header(max_var, max_cls, max_weight);
    } 


    double weight;
    while (c != EOF) {

      if(c == 'c') { // comment
        auto comment = ParseLine(file, c);
        for(auto observer : observers_) {
          observer->Comment(comment);
        }
        continue;
      }

      if (weight_check) {
        ParseDouble(file, c, weight, s_weight); // get weight
        assert (weight >= 0); // bound at least 1
        SkipWhitespace(file, c);
      }

      if(c == 'k') { // cardinality constraint
        statement_type = 'k';
        c = getc_unlocked(file); // skip 'k'
        SkipWhitespace(file, c);
        ParseInteger(file, c, bound); // get bound that follows integer
        assert (bound >= 1); // bound at least 1
        SkipWhitespace(file, c);
      } else if (c == 'g') { // guarded cardinality constraint
        statement_type = 'k';
        c = getc_unlocked(file); // skip 'k'
        SkipWhitespace(file, c);
        ParseInteger(file, c, bound); // get bound that follows integer
        assert (bound >= 1); // bound at least 1
        SkipWhitespace(file, c);
        ParseInteger(file, c, guard); // get guard that follows integer
        SkipWhitespace(file, c);
      } else if (input_type == CAI) {
        statement_type = 'k';
        ParseInteger(file, c, bound); // get bound that follows integer
        assert (bound >= 1); // bound at least 1
        SkipWhitespace(file, c);
      } else { // normal clause
        statement_type = 'c';
      }

      if (input_type != WCARD) {
        ParseClause (file, c, clause);
        if(statement_type == 'c') { // clause
          ncls++;
          for(auto observer : observers_) {
            observer->Clause(clause, weight, s_weight);
          }
        } else if(statement_type == 'k') { // cardinality constraint
          ncls++;
          for(auto observer : observers_) {
            observer->CardinalityConstraint(clause, bound, weight, s_weight, guard);
          }
          guard = 0;
        } 
      } else { // WCARD pb format
        ParseConstraint (file, c, clause, bound);
        if (clause.size()) {
          ncls++;
          for(auto observer : observers_) {
            observer->CardinalityConstraint(clause, bound, weight, s_weight, guard);
          }
          guard = 0;
        }
      }
      SkipWhitespace(file, c);
    }
    fclose(file);

    if (ncls != max_cls) {
      cout << "ERROR incorrect number of clasues parsed" << endl;
      cout << "parsed " << ncls << " expected " << max_cls << endl;
      exit (1);
    }
  }

private:
  static inline void ParseClause(FILE *file, int &current_symbol,
                                      vector<int> &clause);
  static inline void ParseInteger(FILE *file, int &current_symbol,
                                       int& integer);
  static inline string ParseLine(FILE *file, int &current_symbol);
  static inline void SkipWhitespace(FILE *file, int &current_symbol);
  static inline void SkipLinespace(FILE *file, int &current_symbol);

  static inline bool DetermineHeader(FILE *file, int &current_symbol, int &max_var, int &max_cls, int &max_weight, Input_Type &parsed_type);
  static inline void ParseDouble(FILE *file, int &current_symbol,
                                       double &weight, string &s_weight);
  static inline void ParseConstraint(FILE *file, int &current_symbol,
                                      vector<int> &clause, int &bound);
};

void PlainTextKnfParser::ParseClause(
  FILE *file, int &current_symbol, vector<int> &clause) {
  int integer;
  clause.clear();
  do {
    ParseInteger(file, current_symbol, integer);
    clause.emplace_back(integer);
    SkipLinespace(file, current_symbol);
  } while (clause.back() != 0);
  clause.pop_back();
}


void PlainTextKnfParser::ParseConstraint(
  FILE *file, int &current_symbol, vector<int> &clause, int &bound) {
  int integer;

  bound = 1;
  clause.clear();
  do {
    ParseInteger(file, current_symbol, integer); // returns 0 if not a digit
    clause.emplace_back(integer);
    SkipLinespace(file, current_symbol);
    if (current_symbol != '-' && !isdigit(current_symbol)) break;
  } while (clause.back() != 0);
  

  // check for the inequalities
  if (current_symbol == '<') {
    current_symbol = getc_unlocked(file);
    if (current_symbol == '=') {
      current_symbol = getc_unlocked(file); // read '='
      SkipWhitespace(file, current_symbol);
      ParseInteger(file, current_symbol, bound);
      bound = clause.size() - bound;
    } else {
      SkipWhitespace(file, current_symbol);
      ParseInteger(file, current_symbol, bound);
      bound = clause.size() - bound + 1;
    }

    // switch less than to greater than by negating all literals 
    for (int i = 0; i < clause.size(); i++) clause[i] = -1 * clause[i];

  } else if (current_symbol == '>')  {
    current_symbol = getc_unlocked(file);
    if (current_symbol == '=') { // normal at least k
      current_symbol = getc_unlocked(file); // read '='
      SkipWhitespace(file, current_symbol);
      ParseInteger(file, current_symbol, bound);
    } else { // subtract 1 so bound is correct
      SkipWhitespace(file, current_symbol);
      ParseInteger(file, current_symbol, bound);
      bound++;
    }
  } else clause.pop_back();

  SkipLinespace(file, current_symbol);

}

void PlainTextKnfParser::ParseInteger(
  FILE *file, int &current_symbol, int &integer) {
  int sign = current_symbol == '-' ? -1 : 1;
  integer = isdigit(current_symbol) ? current_symbol - '0' : 0;
  while (isdigit(current_symbol = getc_unlocked(file))) {
    integer = integer * 10 + current_symbol - '0';
  }
  integer *= sign;
}

void PlainTextKnfParser::SkipWhitespace(FILE *file, int &current_symbol) {
  while (isspace(current_symbol)) {
    current_symbol = getc_unlocked(file);
  }
}

void PlainTextKnfParser::SkipLinespace(FILE *file, int &current_symbol) {
  while (isspace(current_symbol) && current_symbol != '\n') {
    current_symbol = getc_unlocked(file);
  }
}

string PlainTextKnfParser::ParseLine(FILE *file, int &current_symbol) {
  string line;
  while (current_symbol != '\n' && current_symbol != EOF) {
    line.push_back(current_symbol);
    current_symbol = getc_unlocked(file);
  }
  if(current_symbol != EOF) current_symbol = getc_unlocked(file);
  return line;
}

void PlainTextKnfParser::ParseDouble(
  FILE *file, int &current_symbol, double &weight, string &s_weight) {
  double sign = current_symbol == '-' ? -1.0 : 1.0;
  double remainder = 0;
  int fcnt = 1;
  s_weight = "";
  weight = isdigit(current_symbol) ? current_symbol - '0' : 0;
  s_weight.push_back (current_symbol);
  while (isdigit(current_symbol = getc_unlocked(file))) {
    weight = weight * 10 + current_symbol - '0';
    s_weight.push_back (current_symbol);
  }
  if (current_symbol == '.') { // floating point
    s_weight.push_back (current_symbol);
    while (isdigit(current_symbol = getc_unlocked(file))) {
      remainder = remainder + (current_symbol - '0') / (pow (10 ,fcnt++)) ;
      s_weight.push_back (current_symbol);
    }
  }
  weight += remainder;
  weight *= sign;
}

/*
  receive c pointing to first character of header following p

  if parse cnf, wcnf, knf, wknf
    set parsed_type
    set var, cls, weight
    return true
  else
    return false
*/
bool PlainTextKnfParser::DetermineHeader \
(FILE *file, int &c, int &max_var, int &max_cls, int &max_weight, Input_Type &parsed_type) {
  bool res = false;
  bool weighted = false, knf = false, card = false;

  if (c == 'w') {
    weighted = true;
    c = getc_unlocked(file); // skip 'w'
  }

  if (c == 'k') {
    knf = true;
  } else {
    if (c != 'c') {
      cout << "ERROR incorrect header" << endl;
      exit(1);
    }
  }

  c = getc_unlocked(file); // skip 'c/k'

  if (c == 'a') { // possible card header
    c = getc_unlocked(file); // skip 'a'
    if (c == 'r') {
      c = getc_unlocked(file); // skip 'r'
      if (c == 'd') {
        c = getc_unlocked(file); // skip 'd'
        card = true;
        res = true;
      }
    }
    SkipWhitespace(file, c);
  }

  if (c == 'n') { // normal cnf/knf header
    c = getc_unlocked(file); // skip 'n'
    if (c == 'f') {
       c = getc_unlocked(file); // skip 'f'
      SkipWhitespace(file, c);
      res = true;
    }
  }

  if (res) {
    ParseInteger(file, c, max_var); // get max variables
    assert (max_var >= 1);
    SkipWhitespace(file, c);
    ParseInteger(file, c, max_cls); // get number of clasues
    assert (max_cls >= 1);
    SkipWhitespace(file, c);

    if (weighted) {
      ParseInteger(file, c, max_weight); // get hard weight
      assert (max_weight >= 1);
      SkipWhitespace(file, c);
    }

    SkipWhitespace(file, c);
  }

  // set parsed type
  if (weighted) {
    if (knf) parsed_type = WKNF;
    else if (card) parsed_type = WCARD;
    else parsed_type = WCNF;
  } else {
    if (knf) parsed_type = KNF;
    else parsed_type = CNF;
  }

  return res;
}

#endif
