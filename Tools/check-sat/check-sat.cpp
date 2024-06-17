#include <iostream>
#include <string>
#include "check-sat.hpp"
#include "cnf-partition.hpp"

/*

Input : KNF formula, Assignment

Run: ./check <KNF> <Assignment>

Where the assignment is a list of literals, 
e.g., `1 -2 4 -5`, variable gaps are assigned false (-3)

Output : 
`c VERIFIED` if a satisfying assignment
`c UNVERIFIED <#clauses satisfied> <#clauses unsatisfied>` if not a satifying assignment

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
  
  cout << "check-sat: check if an assignment satisfies a KNF formula." << endl;
  cout << "Run: ./check-sat <KNF> [<Assignment>] [-convert <File>] [-input_type <UNKNOWN,CNF,KNF,WCNF,WKNF,WCARD,CAI>] [-output_type <UNKNOWN,CNF,KNF,WCNF,WKNF,WCARD,CAI>]" << endl;
  
  exit (0);
}


int main(int argc, char* argv[]) {
  
  
  printHelp(argv, argv+argc);

  bool convert, get_input_type, get_output_type, get_solution_type, partition, write_partitions, solFileIn;
  get_input_type = get_output_type = get_solution_type = 0;

  char * convert_file = commandLineParseOption (argv, argv+argc, "-convert", convert);

  char * input_type_string = commandLineParseOption (argv, argv+argc, "-input_type", get_input_type);
  char * output_type_string = commandLineParseOption (argv, argv+argc, "-output_type", get_output_type);
  char * solution_type_string = commandLineParseOption (argv, argv+argc, "-solution_type", get_solution_type);

  char * partition_file = commandLineParseOption (argv, argv+argc, "-partition", partition);

  char * partition_folder = commandLineParseOption (argv, argv+argc, "-pFolder", partition);

  char * sol_file = commandLineParseOption (argv, argv+argc, "-pSol", solFileIn);

  commandLineParseOption (argv, argv+argc, "-write_partitions", write_partitions);

  if (argc < 3 && !convert && !partition) {
    cout << "Error too few arguments: usage is ./check-sat <KNF> [<Assignment>] [options]" << endl;
    exit (1);
  }

  string knf_path = argv[1];

  string assignment_path = argv[2];

  Input_Type input_type = UNKNOWN;
  Input_Type output_type = UNKNOWN;
  Input_Type solution_type = UNKNOWN;

  if (get_input_type) input_type = static_cast<Input_Type> (stoi (input_type_string));
  if (get_output_type) output_type = static_cast<Input_Type> (stoi (output_type_string));
  if (get_solution_type) solution_type = static_cast<Input_Type> (stoi (solution_type_string));

  KnfCheck knfcheck;

  PlainTextKnfParser knf_parser;
  knf_parser.AddObserver(&knfcheck);
  knf_parser.Parse(knf_path, input_type);

  if (partition) {
    if (write_partitions) 
      knfcheck.partition_clauses (partition_folder, partition_file);
    else
      knfcheck.reconstruct_partitioned_solution (partition_folder, partition_file, sol_file);

    return 0;
  }

  bool parsed_ass = knfcheck.parseAssignment(assignment_path, solution_type);

  cout << "Note, casting all weights to integers\n";

  if (parsed_ass) {
    if (knfcheck.has_weight ()) 
      knfcheck.checkMaxSat();
    else 
      knfcheck.checkSat();

    knfcheck.printResult();
  } else cout << "No assignment parsed\n";

  if (convert) {
    if (output_type == CAI)
      knfcheck.writeCai (convert_file);
    else
      knfcheck.writeKnf (convert_file);
  }

  return 0;
}
