// Parser adapted from https://github.com/jreeves3/unsat-proof-skeletons
// Original author Benjamin Kiesl-Ritter, MIT-0 License


#include "cnf2knf.hpp"
// #include<fstream>

namespace cnf2knf {

using namespace std;

bool ParseString(
  FILE *file, int &current_symbol, string s);
  bool ParseStrings(
FILE *file, int &current_symbol, string s1, string s2);
void Parseliterals(
  FILE *file, int &current_symbol, std::vector<int> &literals);
void ParseInteger(
  FILE *file, int &current_symbol, int &integer);
void SkipWhitespace(FILE *file, int &current_symbol);
void SkipLinespace(FILE *file, int &current_symbol);
string ParseLine(FILE *file, int &current_symbol);

bool Cnf_extractor::commandLineParseOption(char ** start, char ** end, const string & marker) {
    char ** position = find(start,end,"-"+marker);
    if ( position == end || ++position == end) return false;
    extractor_options[marker] = string(*position);
    
    return true;
}

bool Cnf_extractor::findOption(char ** start, char ** end, const string & marker) {
    string value;
    bool found = false;
    // true case
    char ** position = find(start,end,"--"+marker+"=true");
    if ( position != end ) {value = "true"; found = true;}
    // false case
    position = find(start,end,"--"+marker+"=false");
    if ( position != end ) {value = "false"; found = true;}
    if (found) extractor_options[marker] = (value);
    
    return found;
}

int Cnf_extractor::parse_options (int argc, char ** argv) {

    commandLineParseOption(argv, argv+argc, "Direct_timeout");
    commandLineParseOption(argv, argv+argc, "Encoded_timeout");
    commandLineParseOption(argv, argv+argc, "Extractor_logging");
    commandLineParseOption(argv, argv+argc, "Engine_logging");
    commandLineParseOption(argv, argv+argc, "BDD_logging");

    findOption (argv, argv+argc, "Direct_AMO");
    findOption (argv, argv+argc, "Direct_AMO_Small");
    findOption (argv, argv+argc, "Encoded_AMO");
    findOption (argv, argv+argc, "Encoded_Others");
    findOption (argv, argv+argc, "Write_KNF");

    return 0;
}


int Cnf_extractor::parse_cnf (char * input_file) {
    FILE* file = fopen(input_file, "r");
    string input_file_s(input_file);
    if (!file) throw "File " + input_file_s + " cannot be opened.";
    
    int c = getc_unlocked(file);
    SkipWhitespace(file, c);
    int statement_type = 0;
    std::vector<int> literals;
    int idx;
    bool found_header = false;
    int nclauses;

    // header
    while (c != EOF) {

      if(c == 'c') { 
        auto comment = ParseLine(file, c);
        continue;
      }
      if(c == 'p') { 
        c = getc_unlocked(file);
        SkipWhitespace(file, c);
        if (!ParseStrings(file, c, "cnf", "knf")) {
                return -1;
        }
        c = getc_unlocked(file);
        SkipWhitespace(file, c);
        ParseInteger(file,c,nvars);
        SkipWhitespace(file, c);
        ParseInteger(file,c,nclauses);
        SkipWhitespace(file, c);
        found_header = true;
        break;
      }
      else break;
    }

   

    if (!found_header) return 1;

    cout << "c Found p cnf header with " << nvars << " variables and " << nclauses << " clauses" << endl;

    while (c != EOF) {

      if(c == 'c') { 
        auto comment = ParseLine(file, c);
        continue;
      }
      
      //      ParseInteger(file, c, idx);
      SkipWhitespace(file, c);

      if(c == 'd' || c == 'r') { // Proof statement is a deletion or restoration
        statement_type = c;
        c = getc_unlocked(file); // skip 'd'/'r'
        SkipWhitespace(file, c);
      } else { // Proof statement is an addition
        statement_type = 'a';
      }
      
      Parseliterals (file, c, literals);
      if(statement_type == 'a') {
        // literals addition
        clauses.push_back (Klause (literals,1));
      } 
      SkipWhitespace(file, c);
    }
    fclose(file);
    return 0; // completed parsing without error
  }

bool ParseString(
  FILE *file, int &current_symbol, string s) {
    string temp_s;
    temp_s = (char) current_symbol;
    for (int i = 0; i < s.length()-1; i++) {
        current_symbol = getc_unlocked(file);
        temp_s += (char) current_symbol;
    }
    // cout << temp_s << endl;
    return (temp_s == s);
  }

bool ParseStrings(
  FILE *file, int &current_symbol, string s1, string s2) {
    string temp_s;
    temp_s = (char) current_symbol;
    for (int i = 0; i < s1.length()-1; i++) {
        current_symbol = getc_unlocked(file);
        temp_s += (char) current_symbol;
    }
    // cout << temp_s << endl;
    return (temp_s == s1 || temp_s == s2 );
  }

void Parseliterals(
  FILE *file, int &current_symbol, std::vector<int> &literals) {
  int integer;
  literals.clear();
  do {
    ParseInteger(file, current_symbol, integer);
    literals.push_back(integer);
    SkipLinespace(file, current_symbol);
  } while (literals.back() != 0);
  literals.pop_back();
}

void ParseInteger(
  FILE *file, int &current_symbol, int &integer) {
  int sign = current_symbol == '-' ? -1 : 1;
  integer = isdigit(current_symbol) ? current_symbol - '0' : 0;
  while (isdigit(current_symbol = getc_unlocked(file))) {
    integer = integer * 10 + current_symbol - '0';
  }
  integer *= sign;
}

void SkipWhitespace(FILE *file, int &current_symbol) {
  while (isspace(current_symbol)) {
    current_symbol = getc_unlocked(file);
  }
}

void SkipLinespace(FILE *file, int &current_symbol) {
  while (isspace(current_symbol) && current_symbol != '\n') {
    current_symbol = getc_unlocked(file);
  }
}

string ParseLine(FILE *file, int &current_symbol) {
  string line;
  while (current_symbol != '\n' && current_symbol != EOF) {
    line.push_back(current_symbol);
    current_symbol = getc_unlocked(file);
  }
  if(current_symbol != EOF) current_symbol = getc_unlocked(file);
  return line;
}


}

