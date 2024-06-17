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


#pragma once

#include <vector>
#include <stdio.h>
#include <fstream>
#include "ilist.h"

// Representations of clauses and sets of clauses

// Clause is a vector of literals, each of which is a negative or positive integer.
// Tautologies are detected and represented as clause of the form -x, x
// Clauses put in canonical ordering with duplicate literals removed, tautologies detected,
// and literals ordered in descending order of the variables
class Clause {
 private:
    ilist contents;
    bool is_tautology;
 public:

    Clause();

    Clause(int *array, size_t len);

    Clause(FILE *infile);

    ~Clause();

    void add(int val);

    size_t length();

    bool tautology();

    int max_variable();

    void canonize();

    void show();

    void show(FILE *outfile);

    void show(std::ofstream &outstream);

    int *data();

    int& operator[](int);

    // Given array mapping (decremented) variable to 0/1
    // determine if clause satisfied
    bool satisfied(char *assignment);

};

// CNF is a collection of clauses.  Can read from a DIMACS format CNF file
class CNF {
 private:
    std::vector<Clause *> clauses;
    int maxVar;
    bool read_failed;

 public:
    CNF();

    // Read clauses DIMACS format CNF file
    CNF(FILE *infile);

    // Did last read fail?
    bool failed();

    // Add a new clause
    void add(Clause *clp);

    // Generate DIMACS CNF representation to stdout, outfile, or outstream
    void show();
    void show(FILE *outfile);
    void show(std::ofstream &outstream);

    // Return number of clauses
    size_t clause_count();
    // Return ID of maximum variable encountered
    int max_variable();

    // Given array mapping (decremented) variable to 0/1
    // determine if every clause satisfied.
    // If not, return ID of first offending clause.  Otherwise return 0
    int satisfied(char *assignment);

    Clause * operator[](int);    
};
