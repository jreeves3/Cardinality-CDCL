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


#ifndef _TBDD_H
#define _TBDD_H

/* Turn on TBDD-specific information in files */
#ifndef ENABLE_TBDD
#define ENABLE_TBDD 1
#endif

/* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

/*============================================
 API for trusted extension to BuDDy BDD package
============================================*/


#include <limits.h>
#include "ilist.h"
#include "bdd.h"

/* Value representing logical truth */
#define TAUTOLOGY INT_MAX 

/* 
   A trusted BDD is one for which a proof has
   been generated showing that it is logically
   entailed by a set of input clauses.
*/
/*
  A trusted BDD must have a reference count >= 1, or else
  it's validating clause will be deleted.
  Consequently, all operations that a return a TBDD
  have an incremented reference count.  
 */
typedef struct {
    BDD root;
    int clause_id;  /* Id of justifying clause */
    int rc_index;   /* Index of reference counter */
} TBDD;

#ifndef CPLUSPLUS
typedef TBDD tbdd;
#endif

#ifdef CPLUSPLUS
extern "C" {
#endif


/*============================================
  Package setup.
============================================*/

/* 
  Set up package.  Arguments:
  - proof output file
  - number of variables in CNF

  When generating LRAT proofs, also require arguments:
  - Number of clauses in CNF
  - The list of clauses, where clause i is at clauses[i-1]
  
  These functions also initialize BuDDy, using parameters tuned according
  to the predicted complexity of the operations.

  Return 0 if OK, otherwise error code
*/

/* Supported proof types */
   typedef enum { PROOF_LRAT, PROOF_DRAT, PROOF_FRAT, PROOF_NONE } proof_type_t;

   extern int tbdd_init(FILE *pfile, int *variable_counter, int *clause_id_counter, ilist *input_clauses, ilist variable_ordering, proof_type_t ptype, bool binary);

/* 
   Initializers specific for the seven combinations of proof formats
 */
extern int tbdd_init_lrat(FILE *pfile, int variable_count, int clause_count, ilist *input_clauses, ilist variable_ordering);
extern int tbdd_init_lrat_binary(FILE *pfile, int variable_count, int clause_count, ilist *input_clauses, ilist variable_ordering);
extern int tbdd_init_drat(FILE *pfile, int variable_count);
extern int tbdd_init_drat_binary(FILE *pfile, int variable_count);
extern int tbdd_init_frat(FILE *pfile, int *variable_counter, int *clause_id_counter);
extern int tbdd_init_frat_binary(FILE *pfile, int *variable_counter, int *clause_id_counter);
extern int tbdd_init_noproof(int variable_count, ilist variable_ordering);

/*
  Deallocate all resources used by TBDD.
  If verbosity >= 1, print summary information
 */
extern void tbdd_done();

/*
  Report statistics for BDDs and TBDDs
 */    
extern void bdd_report();
extern void tbdd_report();

/*
  Functions that can be added to provide more data on exit.
  Function takes verbosity level as argument.
 */
typedef void (*tbdd_info_fun)(int);

void tbdd_add_info_fun(tbdd_info_fun f);

typedef void (*tbdd_done_fun)(void);

void tbdd_add_done_fun(tbdd_done_fun f);

/*
  Setting optional solver features
 */

/* Verbosity levels:

   0: Totally silent
   1: Summary information (default)
   2: Enable comments in generated proof
   3: Debugging information
*/
extern void tbdd_set_verbose(int level);

/* 
   Set limit on the number of input+proof clauses.
   Setting to 0 will keep at default limit (1<<30).
 */
extern void tbdd_set_clause_limit(int clim);

/*============================================
 Creation and manipulation of trusted BDDs
============================================*/

/*
  Print information about TBDD
 */
void tbdd_print(TBDD r, FILE *out);

/*
  Create a fresh TBDD.  Increment reference count for BDD
  and initialize reference count for TBDD
 */
TBDD tbdd_create(BDD r, int clause_id);

/*
  Increment/decrement reference count for BDD
 */
extern TBDD tbdd_addref(TBDD tr);
extern void tbdd_delref(TBDD tr);

/* 
   proof_step = TAUTOLOGY
   root = 1
 */
extern TBDD TBDD_tautology();

/* 
   proof_step = TAUTOLOGY
   root = 0 (Used as an error return)
 */

extern TBDD TBDD_null();

/*
   Test whether underlying BDD is 0/1
 */
extern bool tbdd_is_true(TBDD tr);
extern bool tbdd_is_false(TBDD tr);

/*
  Generate BDD representation of specified input clause.
  Generate proof that BDD will evaluate to TRUE
  for all assignments satisfying clause.

  clause_id should be number between 1 and the number of input clauses
 */

extern TBDD tbdd_from_clause(ilist clause);  // For DRAT
extern TBDD tbdd_from_clause_id(int id);     // For LRAT

/*
  Generate BDD representation of XOR.
  For DRAT
 */
extern TBDD TBDD_from_xor(ilist variables, int phase);

/* Operations on TBDDs */
extern TBDD      tbdd_and(TBDD, TBDD);

/*
  Upgrade ordinary BDD to TBDD by proving
  implication from another TBDD
 */
extern TBDD tbdd_validate(BDD r, TBDD tr);

/*
  Declare BDD to be trustworthy.  Proof
  checker must provide validation.
  Only works when generating DRAT proofs
 */
extern TBDD TBDD_trust(BDD r);

/*
  Form conjunction of two TBDDs and prove
  their conjunction implies the new one
 */
extern TBDD tbdd_and(TBDD tr1, TBDD tr2);

/*
  Form conjunction of TBDDs tl & tr.  Use to validate
  BDD r
 */
extern TBDD tbdd_validate_with_and(BDD r, TBDD tl, TBDD tr);

/*
  Validate that a clause is implied by a TBDD.
  Use this version when generating LRAT proofs
  Returns clause id.
 */
extern int tbdd_validate_clause(ilist clause, TBDD tr);

/*
  Assert that a clause holds.  Proof checker
  must provide validation.
  Use this version when generating DRAT proofs,
  or when don't want to provide antecedent in FRAT proof
  Returns clause id.
 */
extern int assert_clause(ilist clause);

/*============================================
 Useful BDD operations
============================================*/

/* Construct BDD representation of a clause */
extern BDD BDD_build_clause(ilist literals);
/* Construct BDD representation of XOR (phase = 1) or XNOR (phase = 0) */
extern BDD BDD_build_xor(ilist variables, int phase);

/* Represent conjunction of literals (a "cube") as a BDD or an ilist */
extern BDD BDD_build_cube(ilist literals);
extern ilist BDD_decode_cube(BDD r);

#ifdef CPLUSPLUS
}
#endif

#ifndef CPLUSPLUS
#define tbdd_tautology TBDD_tautology
#define tbdd_from_xor TBDD_from_xor
#define tbdd_null TBDD_null
#endif

#ifdef CPLUSPLUS
/*============================================
 C++ interface
============================================*/
namespace trustbdd {
class tbdd
{
 public:

    tbdd(const bdd &r, const int &id) { tb = tbdd_create(r.get_BDD(), id); }
    tbdd(const tbdd &t)               { tb = tbdd_addref(t.tb); }
    tbdd(TBDD tr)                     { tb = tr; }  
    tbdd(void)                        { tb = TBDD_tautology(); } 

    ~tbdd(void)                       { tbdd_delref(tb); }

    tbdd operator=(const tbdd &tr)    { if (tb.root != tr.tb.root) { tbdd_delref(tb); tb = tbdd_addref(tr.tb); } return *this; }
    // Backdoor functions provide read-only access
    bdd get_root()                     { return bdd(tb.root); }
    int get_clause_id()                { return tb.clause_id; }

 private:
    TBDD tb;

    friend void tbdd_print(tbdd &tr, FILE *out);
    friend tbdd tbdd_tautology(void);
    friend tbdd tbdd_null(void);
    friend bool tbdd_is_true(tbdd &tr);
    friend bool tbdd_is_false(tbdd &tr);
    friend tbdd tbdd_and(tbdd &tl, tbdd &tr);
    friend tbdd tbdd_validate(bdd r, tbdd &tr);
    friend tbdd tbdd_validate_with_and(bdd r, tbdd &tl, tbdd &tr);
    friend tbdd tbdd_trust(bdd r);
    friend int tbdd_validate_clause(ilist clause, tbdd &tr);
    friend tbdd tbdd_from_xor(ilist variables, int phase);
    friend int tbdd_nameid(tbdd &tr);
    friend bdd bdd_build_xor(ilist literals);
    friend bdd bdd_build_clause(ilist literals);
    friend bdd bdd_build_cube(ilist literals);
    friend ilist bdd_decode_cube(bdd &r);

    // Convert to low-level form
    friend void tbdd_xfer(tbdd &tr, TBDD &res);
};

inline void tbdd_print(tbdd &tr, FILE *out)
{ tbdd_print(tr.tb, out); } 

inline tbdd tbdd_tautology(void)
{ return tbdd(TBDD_tautology()); }

inline tbdd tbdd_null(void)
{ return tbdd(TBDD_null()); }

inline bool tbdd_is_true(tbdd &tr)
{ return tr.tb.root == bdd_true().get_BDD(); }

inline bool tbdd_is_false(tbdd &tr)
{ return tr.tb.root == bdd_false().get_BDD(); }

inline tbdd tbdd_and(tbdd &tl, tbdd &tr)
{ return tbdd(tbdd_and(tl.tb, tr.tb)); }

inline tbdd tbdd_validate(bdd r, tbdd &tr)
{ return tbdd(tbdd_validate(r.get_BDD(), tr.tb)); }

inline tbdd tbdd_validate_with_and(bdd r, tbdd &tl, tbdd &tr)
{ return tbdd(tbdd_validate_with_and(r.get_BDD(), tl.tb, tr.tb)); }

inline tbdd tbdd_trust(bdd r)
{ 
    TBDD T = TBDD_trust(r.get_BDD());
    return tbdd(T);
}

inline int tbdd_validate_clause(ilist clause, tbdd &tr)
{ return tbdd_validate_clause(clause, tr.tb); }

inline tbdd tbdd_from_xor(ilist variables, int phase)
{ return tbdd(TBDD_from_xor(variables, phase)); }

inline int tbdd_nameid(tbdd &tr)
{ return bdd_nameid(tr.tb.root); }

inline bdd bdd_build_xor(ilist variables, int phase)
{ return bdd(BDD_build_xor(variables, phase)); }

inline bdd bdd_build_clause(ilist literals)
{ return bdd(BDD_build_clause(literals)); }

inline bdd bdd_build_cube(ilist literals)
{ return bdd(BDD_build_cube(literals)); }

inline ilist bdd_decode_cube(bdd &r)
{ return BDD_decode_cube(r.get_BDD()); }



} /* Namespace trustbdd */
#endif /* CPLUSPLUS */

#endif /* _TBDD_H */
/* EOF */


