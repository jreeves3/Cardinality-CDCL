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


#include <iostream>
#include <ctype.h>
#include "clause.hpp"
#include <algorithm>
#include <cstring>

static int skip_line(FILE *infile) {
  int c;
  while ((c = getc(infile)) != EOF) {
    if (c == '\n')
      return c;
  }
  return c;
}

// Put literals in descending order of the variables
static bool abs_less(int x, int y) {
  return abs(x) > abs(y);
}


Clause::Clause() { contents = ilist_new(0); is_tautology = false; }

Clause::~Clause() { ilist_free(contents); }

Clause::Clause(int *array, size_t len) {
  is_tautology = false;
  contents = ilist_new(len);
  for (int i = 0; i < len; i++)
    add(array[i]);
  canonize();
}

Clause::Clause(FILE *infile) {
  int rval;
  int lit;
  int c;
  is_tautology = false;
  contents = ilist_new(4);

  // Skip blank lines and comments
  while ((c = getc(infile)) != EOF) {
    if (c == 'c')
      c = skip_line(infile);
    if (isspace(c))
      continue;
    else {
      ungetc(c, infile);
      break;
    }
  }

  while ((rval = fscanf(infile, "%d", &lit)) == 1) {
    if (lit == 0)
      break;
    else
      add(lit);
  }
  canonize();
}

void Clause::add(int val) {
  contents = ilist_push(contents, val);
}

size_t Clause::length() {
  if (is_tautology)
    return 0;
  return ilist_length(contents);
}

bool Clause::tautology() {
  return is_tautology;
}

int Clause::max_variable() {
  int mvar = 0;
  if (is_tautology)
    return 0;
  for (int i = 0; i < length(); i++) {
    int var = abs(contents[i]);
    mvar = std::max(var, mvar);
  }
  return mvar;
}

int * Clause::data() {
  return contents;
}

int& Clause::operator[](int i) {
  return contents[i];
}

bool Clause::satisfied(char *assignment) {
    bool found = is_tautology;
    for (int i = 0; !found && i < ilist_length(contents); i++) {
	int lit = contents[i];
	found = (lit < 0 && assignment[-lit-1] == 0) || (lit > 0 && assignment[lit-1] == 1);
    }
    return found;
}

void Clause::canonize() {
  std::sort(contents, contents + length(), abs_less);
  int last_lit = 0;
  size_t read_pos = 0;
  size_t write_pos = 0;
  while(read_pos < length()) {
    int lit = contents[read_pos++];
    if (abs(lit) == abs(last_lit)) {
      if (lit != last_lit) {
	// Opposite literals encountered
	is_tautology = true;
	break;
      }
    } else {
      contents[write_pos++] = lit;
    }
    last_lit = lit;
  }
  if (is_tautology) {
    contents = ilist_resize(contents, 2);
    contents[0] = abs(last_lit);
    contents[1] = -abs(last_lit);
  } else
    contents = ilist_resize(contents, write_pos);
}

void Clause::show() {
  if (is_tautology)
    std::cout << "c Tautology" << std::endl;
  for (int i = 0; i < length(); i++)
    std::cout << contents[i] << ' ';
  std::cout << '0' << std::endl;
}

void Clause::show(std::ofstream &outstream) {
  if (is_tautology)
    outstream << "c Tautology" << std::endl;
  for (int i = 0; i < length(); i++)
    outstream << contents[i] << ' ';
  outstream << '0' << std::endl;
}


void Clause::show(FILE *outfile) {
  if (is_tautology)
    fprintf(outfile, "c Tautology\n");
  for (int i = 0; i < length(); i++)
    fprintf(outfile, "%d ", contents[i]);
  fprintf(outfile, "0\n");
}

CNF::CNF() { read_failed = false; maxVar = 0; }

CNF::CNF(FILE *infile) { 
  int expectedMax = 0;
  int expectedCount = 0;
  read_failed = false;
  maxVar = 0;
  int c;
  // Look for CNF header
  while ((c = getc(infile)) != EOF) {
    if (isspace(c)) 
      continue;
    if (c == 'c')
      c = skip_line(infile);
    if (c == EOF) {
      std::cerr << "Not valid CNF File.  No header line found" << std::endl;
      read_failed = true;
      return;
    }
    if (c == 'p') {
      char field[20];
      if (fscanf(infile, "%s", field) != 1) {
	std::cerr << "Not valid CNF FILE.  No header line found" << std::endl;
	read_failed = true;
	return;
      }
      if (strcmp(field, "cnf") != 0) {
	std::cerr << "Not valid CNF file.  Header shows type is '" << field << "'" << std::endl;
	read_failed = true;
	return;
      }
      if (fscanf(infile, "%d %d", &expectedMax, &expectedCount) != 2) {
	std::cerr << "Invalid CNF header" << std::endl;
	read_failed = true;
	return;
      } 
      c = skip_line(infile);
      break;
    }
    if (c == EOF) {
      read_failed = true;
      std::cerr << "EOF encountered before reading any clauses" << std::endl;
      return;
    }
  }
  while (1) {
    Clause *clp = new Clause(infile);
    if (clp->length() == 0)
      break;
    add(clp);
    int mvar = clp->max_variable();
    maxVar = std::max(maxVar, mvar);
  }
  if (maxVar > expectedMax) {
    std::cerr << "Encountered variable " << maxVar << ".  Expected max = " << expectedMax << std::endl;
    read_failed = true;
    return;
  }
  if (clause_count() != expectedCount) {
    std::cerr << "Read " << clause_count() << " clauses.  Expected " << expectedCount << std::endl;
    read_failed = true;
    return;
  }
}

bool CNF::failed() {
  return read_failed;
}

void CNF::add(Clause *clp) {
  clauses.push_back(clp);
}

Clause * CNF::operator[](int i) {
  return clauses[i];
}


void CNF::show() {
  std::cout << "p cnf " << maxVar << " " << clause_count() << std::endl;
  for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
    (*clp)->show();
  }
}

void CNF::show(std::ofstream &outstream) {
  outstream << "p cnf " << maxVar << " " << clause_count() << std::endl;
  for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
    (*clp)->show(outstream);
  }
}

void CNF::show(FILE *outfile) {
  fprintf(outfile, "p cnf %d %d\n", maxVar, (int) clause_count());
  for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
    (*clp)->show(outfile);
  }
}

size_t CNF::clause_count() {
  return clauses.size();
}

int CNF::max_variable() {
  return maxVar;
}

int CNF::satisfied(char *assignment) {
    for (int cid = 1; cid <= clauses.size(); cid++) {
	Clause *cp = clauses[cid-1];
	if (!cp->satisfied(assignment))
	    return cid;
    }
    return 0;
}
