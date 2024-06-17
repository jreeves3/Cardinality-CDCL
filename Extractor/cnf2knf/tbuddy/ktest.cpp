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

#include <sys/time.h>
#include "clause.hpp"
#include "eval.hpp"

using namespace std;
using namespace trustbdd;

int verblevel = 1;

unsigned seed = 123456;

/* Test ability to check cardinality constraints */

void usage(char *name) {
    printf("Usage: %s [-h] [-v VERB] NVAR file.cnf\n", name);
    printf("  -h      Print this message\n");
    printf("  -v VERB Set verbosity level\n");
    printf("  NDATA   Number of data variables\n");
}

double tod() {
    struct timeval tv;
    if (gettimeofday(&tv, NULL) == 0)
	return (double) tv.tv_sec + 1e-6 * tv.tv_usec;
    else
	return 0.0;
}

bool run(CNF *formula, int ndata) {
    vector<int> lits;
    int upper, lower;
    Ordering O(formula->max_variable(), ndata, verblevel);
    for (int i = 0; i < formula->clause_count(); i++) {
	Clause *cp = (*formula)[i];
	O.add_clause(cp->data(), cp->length());
    }
    ilist ordering = O.generate_ordering(seed);
    if (ordering && verblevel >= 2) {
	printf("c Variable ordering: ");
	ilist_print(ordering, stdout, " ");
	printf("\n");
    }
    TermSet T(formula->max_variable(), ndata, ordering, verblevel);
    int tid = 0;
    for (int i = 0; i < formula->clause_count() && tid >= 0; i++) {
	Clause *cp = (*formula)[i];
	tid = T.add_clause(cp->data(), cp->length());
    }
    if (tid < 0)
	return false;
    if (verblevel >= 1) {
	cout << "c Read " << formula->clause_count() << " clauses" << endl;
    }
    if (!T.bucket_reduce()) {
	cout << "Bucket reduce failed" << std::endl;
	return false;
    } else if (verblevel >= 2) {
	cout << "Bucket reduction succeeded" << endl;
    }
    if (!T.cardinality_converter(lits, &lower, &upper)) {
	cout << "Failed to extract cardinality constraints" << std::endl;
	return false;
    } else if (verblevel >= 2) {
	cout << "Found constraint with lower = " << lower << " and upper = " << upper << endl;
    }
    int kcount = 0;
    if (lower > 0)
	kcount++;
    if (upper < ndata)
	kcount++;
    cout << "p knf " << ndata << " " << kcount << endl;
    if (lower > 0) {
	if (lower != 1)
	    cout << "k " << lower << " ";
	for (int lit : lits)
	    cout << lit << " ";
	cout << "0" << endl;
    }
    if (upper < ndata) {
	int lim = ndata-upper;
	if (lim != 1)
	    cout << "k " << lim << " ";
	for (int lit : lits)
	    cout << -lit << " ";
	cout << "0" << endl;
    }
    if (verblevel >= 1) {
	T.show_statistics();
    }
    return true;
}


int main(int argc, char *argv[]) {
    int argi = 1;
    while (argi < argc && argv[argi][0] == '-') {
	switch (argv[argi][1]) {
	case 'h':
	    usage(argv[0]);
	    return 0;
	case 'v':
	    if (++argi >= argc) {
		usage(argv[0]);
		return 1;
	    }
	    verblevel = atoi(argv[argi]);
	    argi++;
	    break;
	default:
	    usage(argv[0]);
	    return 1;
	}
    }
    if (argi + 1 >= argc) {
	usage(argv[0]);
	return 1;
    }
    int ndata = atoi(argv[argi++]);
    char *fname = argv[argi];
    FILE *infile = fopen(fname, "r");
    if (!infile) {
	cout << "ERROR: Couldn't open file " << fname << endl;
	return 1;
    }
    double start = tod();
    CNF *formula = new CNF(infile);
    if (formula->failed()) {
	cout << "Failed to read CNF file " << fname << endl;
	return 1;
    }
    bool ok = run(formula, ndata);
    if (verblevel >= 1) {
	printf("c Elapsed seconds: %.3f\n", tod()-start);
	cout << "c " << (ok ? "Success" : "Failure") << endl;
    }
    return ok ? 0 : 1;
}    
