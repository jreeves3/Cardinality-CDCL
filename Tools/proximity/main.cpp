#include <iostream>
#include <string>
#include "main.hpp"

/*

This script parses a KNF formula and returns a variable ordering by

  1. Parsing the formula
  2. Computing the proximity algorithm
  3. Printing the ordering

Execution: 

  > ./proximity <KNF> > <ORDER>


Note, the input KNF can include AMO constraint information with additional lines,

  m <bound> <literals> 0

Code adapted from unsat-proof-skeletons (Amazon project on github)

*/


char* commandLineParseOption(char ** start, char ** end, const string & marker, bool &found) {
  char ** position = find(start,end,marker);
  found = false;
  if ( position != end ) found = true;
  if ( ++position == end) {return 0;}
  return *position;
}

void printHelp(char ** start, char ** end) {
  char ** position = find(start,end,"-h");
  if ( position == end ) return;
  
  cout << "Generate proximity ordering for cardinality constraint variables." << endl;
  cout << "Run: ./proximity <KNF>" << endl;
  
  exit (0);
}


int main(int argc, char* argv[]) {
  
  
  printHelp(argv, argv+argc);

  bool bias_input = false;
  
  // Additional arguments possible but not included in AAAI paper
  char * bias_string = commandLineParseOption (argv, argv+argc, "-bias", bias_input);

  if (argc < 1) {
    cout << "Error too few arguments: usage is ./check-sat <KNF> [<Assignment>] [options]" << endl;
    exit (1);
  }

  string knf_path = argv[1];

  KnfProx knfprox;
  Input_Type input_type = KNF;

  float bias_change = 0;

  if (bias_input) {
    bias_change = stof(bias_string);
  }

  PlainTextKnfParser knf_parser;
  knf_parser.AddObserver(&knfprox);

  // 1. Parse the KNF
  knf_parser.Parse(knf_path, input_type);

  // 2. Get the proximity
  knfprox.get_proximity(bias_change);

  // 3. Print the ordered KNF formula
  knfprox.print_ordered_knf ();

  return 0;
}
