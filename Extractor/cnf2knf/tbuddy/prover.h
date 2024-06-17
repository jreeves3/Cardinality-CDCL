/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
  This code was not included in the original BuDDy distribution and is
  therefore not subject to any of its licensing terms.

  Permission is hereby granted, free of
  charge, to any person obtaining a copy of this software and
  associated documentation files (the "Software"), to deal in the
  Software without restriction, including without limitation the
  rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom
  the Software is furnished to do so, subject to the following
  conditions:
  
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


/* Routines to manage proof generation */

#ifndef PROVER_H
#define PROVER_H

#include <stdarg.h>

/* Size limits */
/* Maximum number of clauses for each proof type */
#define CLAUSE_LIMIT_LRAT ((1<<30) + ((1<<30) - 16))
#define CLAUSE_LIMIT_FRAT (1<<27)
#define CLAUSE_LIMIT_DRAT (1<<25)

/* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

#ifdef CPLUSPLUS
extern "C" {
#endif

/* Global variables exported by prover */
extern proof_type_t proof_type;
extern int verbosity_level;
extern int clause_limit;
extern int *variable_counter;
extern int *clause_id_counter;
extern int total_clause_count;
extern int input_variable_count;
extern int input_clause_count;
extern int max_live_clause_count;
extern int deleted_clause_count;

/* Prover setup and completion */
extern int prover_init(FILE *pfile, int *variable_counter, int *clause_counter, ilist *clauses, ilist variable_ordering, proof_type_t ptype, bool binary);
extern void prover_done();

/* Put literals in clause in canonical order */
extern ilist clean_clause(ilist clause);

/* Return clause ID */
/* For DRAT proof, antecedents can be NULL */
extern int generate_clause(ilist literals, ilist antecedent);

/* For FRAT, have special clauses */
extern void insert_frat_clause(FILE *pfile, char cmd, int clause_id, ilist literals, bool binary);

extern void delete_clauses(ilist clause_ids);

/* Some deletions must be deferred until top-level apply completes */
extern void defer_delete_clause(int clause_id);
extern void process_deferred_deletions();


    
/* Retrieve input clause.  NULL if invalid */
extern ilist get_input_clause(int id);

/* 
   Fill ilist with defining clause.
   ils should be big enough for 3 elemeents.
   Return either the list of literals or TAUTOLOGY_CLAUSE 
*/
extern ilist defining_clause(ilist ils, dclause_t dtype, int nid, int vid, int hid, int lid);

/* Print clause */
extern void print_clause(FILE *out, ilist clause);

/*
  Determine whether information can be printed to proof file.
  Do so only when printing LRAT format and verbosity level is sufficiently high
 */
extern bool print_ok(int vlevel);

/*
  Print comment in proof. Don't need to include "c" in string.
  Only will print when verbosity level at least that specified
  Newline printed at end
 */

extern void print_proof_comment(int vlevel, const char *fmt, ...);

/*
  Support for generating apply operation proofs.
 */

    

#ifdef CPLUSPLUS
}
#endif

#endif /* PROVER_H */

/* EOF */
