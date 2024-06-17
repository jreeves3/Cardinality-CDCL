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


#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "tbdd.h"
#include "kernel.h"


/*============================================
  Local data
============================================*/

#define BUFLEN 2048
// For formatting information
static char ibuf[BUFLEN];

#define FUN_MAX 10
static tbdd_info_fun ifuns[FUN_MAX];
static int ifun_count = 0;

static tbdd_done_fun dfuns[FUN_MAX];
static int dfun_count = 0;

static int last_variable = 0;
static int last_clause_id = 0;


/* Unit clauses that have not been deleted */
static ilist created_unit_clauses;
/* Unit clauses that (should) have been deleted */
static ilist dead_unit_clauses;

/* Managing reference counts for TBDDs */

/*
  Each newly created TBDD gets assigned an index into a table of
  reference counts.  Once the RC for a TBDD drops to 0, its unit
  clause can be deleted.
 */

/* Table parameters */
#define TABLE_INIT_SIZE 1024
//#define TABLE_INIT_SIZE 1
#define TABLE_SCALE 2

/* Table of references */
static int *rc_table = NULL;
/* Number of allocated table entries */
static int rc_allocated_count = 0;
/*
  Head of free list.  Free list threads through unused table
  positions, terminating with value -1
*/
static int rc_freepos;

/*============================================
  Local functions
============================================*/
static int new_unit_clause(int id) {
    if (id != TAUTOLOGY)
	created_unit_clauses = ilist_push(created_unit_clauses, id);
    return id;
}

/* Initialize the RC table */
static void rc_init() {
    rc_allocated_count = TABLE_INIT_SIZE;
    rc_table = calloc(rc_allocated_count, sizeof(int));
    if (!rc_table) {
	fprintf(ERROUT, "Couldn't allocate space for %d RC table entries\n", rc_allocated_count);
	bdd_error(BDD_MEMORY);
	return;
    }
    rc_table[rc_allocated_count-1] = -1;
    int rci;
    for (rci = rc_allocated_count-2; rci >= 0; rci--)
	rc_table[rci] = rci+1;
    rc_freepos = 0;
}

/* Dispose of RC table */
static void rc_done() {
    free(rc_table);
}

/* Grow the table */
static void rc_grow() {
    int nsize = rc_allocated_count * TABLE_SCALE;
    rc_table = realloc(rc_table, nsize*sizeof(int));
    if (!rc_table) {
	fprintf(ERROUT, "Couldn't allocate space for %d RC table entries\n", rc_allocated_count);
	bdd_error(BDD_MEMORY);
	return;
    }
    rc_table[nsize-1] = -1;
    int rci;
    for (rci = nsize-2; rci >= rc_allocated_count; rci--)
	rc_table[rci] = rci+1;
    rc_freepos = rc_allocated_count;
    rc_allocated_count = nsize;
}

static int rc_new_entry(int clause_id) {
    if (clause_id == TAUTOLOGY)
	return -1;
    if (rc_freepos == -1)
	rc_grow();
    int rci = rc_freepos;
    rc_freepos = rc_table[rci];
    rc_table[rci] = 1;
    return rci;
}

static void rc_dispose(int rci) {
    rc_table[rci] = rc_freepos;
    rc_freepos = rci;
}

static int rc_get(int rci) {
    if (rci == -1)
	return 1;
    if (rci < -1 || rci >= rc_allocated_count) {
	fprintf(ERROUT, "Invalid RC index %d\n", rci);
	bdd_error(BDD_RANGE);
	return 0;
    }
    return rc_table[rci];
}

static void rc_increment(int rci) {
    if (rci == -1)
	/* TAUTOLOGY */
	return;
    if (rci < -1 || rci >= rc_allocated_count) {
	fprintf(ERROUT, "Invalid RC index %d\n", rci);
	bdd_error(BDD_RANGE);
	return;
    }
    if (rc_table[rci] == 0)
	fprintf(ERROUT, "WARNING: Incrementing RC[%d] to 1\n", rci);
    rc_table[rci]++;
}

static int rc_decrement(int rci) {
    if (rci == -1)
	/* TAUTOLOGY */
	return 1;
    if (rci < -1 || rci >= rc_allocated_count) {
	fprintf(ERROUT, "Invalid RC index %d\n", rci);
	bdd_error(BDD_RANGE);
	return 0;
    }
    int nval = rc_table[rci]-1;
    if (nval < 0)
	fprintf(ERROUT, "WARNING.  Decrementing RC[%d] to %d\n", rci, nval);
    rc_table[rci] = nval;
    return nval;
}


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
  
  When generating DRAT proofs, can provide NULL for argument input_clauses.

  These functions also initialize BuDDy, using parameters tuned according
  to the predicted complexity of the operations.

  Returns 0 if OK, otherwise error code
*/

int tbdd_init(FILE *pfile, int *variable_counter, int *clause_id_counter, ilist *input_clauses, ilist variable_ordering, proof_type_t ptype, bool binary) {
    created_unit_clauses = ilist_new(100);
    dead_unit_clauses = ilist_new(100);
    rc_init();
    return prover_init(pfile, variable_counter, clause_id_counter, input_clauses, variable_ordering, ptype, binary);
}

int tbdd_init_lrat(FILE *pfile, int variable_count, int clause_count, ilist *input_clauses, ilist variable_ordering) {
    last_variable = variable_count;
    last_clause_id = clause_count;
    return tbdd_init(pfile, &last_variable, &last_clause_id, input_clauses, variable_ordering, PROOF_LRAT, false);
}

int tbdd_init_lrat_binary(FILE *pfile, int variable_count, int clause_count, ilist *input_clauses, ilist variable_ordering) {
    last_variable = variable_count;
    last_clause_id = clause_count;
    return tbdd_init(pfile, &last_variable, &last_clause_id, input_clauses, variable_ordering, PROOF_LRAT, true);
}

int tbdd_init_drat(FILE *pfile, int variable_count) {
    last_variable = variable_count;
    last_clause_id = 0;
    int result = tbdd_init(pfile, &last_variable, &last_clause_id, NULL, NULL, PROOF_DRAT, false);
    tbdd_set_clause_limit(CLAUSE_LIMIT_DRAT);
    return result;
}

int tbdd_init_drat_binary(FILE *pfile, int variable_count) {
    last_variable = variable_count;
    last_clause_id = 0;
    int result = tbdd_init(pfile, &last_variable, &last_clause_id, NULL, NULL, PROOF_DRAT, true);
    tbdd_set_clause_limit(CLAUSE_LIMIT_DRAT);
    return result;
}

int tbdd_init_frat(FILE *pfile, int *variable_counter, int *clause_id_counter) {
    //    printf("c INITIALIZING TBDD\n");
    int result = tbdd_init(pfile, variable_counter, clause_id_counter, NULL, NULL, PROOF_FRAT, false);
    tbdd_set_clause_limit(CLAUSE_LIMIT_FRAT);
    return result;
}

int tbdd_init_frat_binary(FILE *pfile, int *variable_counter, int *clause_id_counter) {
    int result = tbdd_init(pfile, variable_counter, clause_id_counter, NULL, NULL, PROOF_FRAT, false);
    tbdd_set_clause_limit(CLAUSE_LIMIT_FRAT);
    return result;
}

int tbdd_init_noproof(int variable_count, ilist variable_ordering) {
    last_variable = variable_count;
    return tbdd_init(NULL, &last_variable, NULL, NULL, variable_ordering, PROOF_NONE, false);
}

void tbdd_set_verbose(int level) {
    verbosity_level = level;
}

void tbdd_set_clause_limit(int clim) {
    if (clim <= 0)
	return;
    if (clim > INT_MAX-4)
	clim = INT_MAX-4;
    clause_limit = clim;
}

void bdd_report() {
    if (verbosity_level >= 1) {
	bddStat s;
	bdd_stats(&s);
	bdd_printstat();
	printf("\nc BDD statistics\n");
	printf("c ----------------\n");
	printf("c Total BDD nodes produced: %ld\n", s.produced);
    }
}

void tbdd_report() {
    int i;
    if (verbosity_level >= 1) {
	printf("c Input variables: %d\n", input_variable_count);
	printf("c Input clauses: %d\n", input_clause_count);
	if (clause_id_counter) {
	    printf("c Total clauses: %d\n", total_clause_count);
	    int unused = *clause_id_counter - total_clause_count;
	    double upct = 100.0 * (double) unused/total_clause_count;
	    printf("c Unused+non-BDD clause IDs: %d (%.1f%%)\n", unused, upct);
	    printf("c Maximum live clauses: %d\n", max_live_clause_count);
	    printf("c Deleted clauses: %d\n", deleted_clause_count);
	    printf("c Final live clauses: %d\n", total_clause_count-deleted_clause_count);
	}
	if (variable_counter)
	    printf("c Total variables: %d\n", *variable_counter);
    }
    for (i = 0; i < ifun_count; i++) {
	ifuns[i](verbosity_level);
    }
}


void tbdd_done() {
    /* Find difference of the created/dead unit clauses */
    ilist_sort(created_unit_clauses);
    ilist_sort(dead_unit_clauses);
    int ic = 0;
    int id = 0;
    ilist live_unit_clauses = ilist_new(100);
    while (ic < ilist_length(created_unit_clauses) && id < ilist_length(dead_unit_clauses)) {
	int cc = created_unit_clauses[ic];
	int cd = dead_unit_clauses[id];
	if (cc < cd) {
	    live_unit_clauses = ilist_push(live_unit_clauses, cc);
	    ic++;
	} else if (cc == cd) {
	    ic++; id++;
	} else {
	    fprintf(ERROUT, "ERROR: Unit clause %d dead but never created\n", cd);
	    id++;
	}
    }
    while (ic < ilist_length(created_unit_clauses))
	live_unit_clauses = ilist_push(live_unit_clauses, created_unit_clauses[ic++]);
    while (id < ilist_length(dead_unit_clauses))
	fprintf(ERROUT, "ERROR: Unit clause %d dead but never created\n", dead_unit_clauses[id++]);

    /* Delete outstanding unit clauses */
    if (ilist_length(live_unit_clauses) > 0) {
	print_proof_comment(2, "Delete remaining unit clauses");
	delete_clauses(live_unit_clauses);
    }
    if (false && verbosity_level >= 2) {
	printf("c Unit clauses: Created %d.  Deleted %d.  Remaining = [",
	       ilist_length(created_unit_clauses), ilist_length(dead_unit_clauses));
	if (ilist_length(live_unit_clauses) > 20) {
	    ilist_resize(live_unit_clauses, 20);
	    ilist_print(live_unit_clauses, stdout, " ");
	    printf(" ...]\n");
	} else {
	    ilist_print(live_unit_clauses, stdout, " ");
	    printf("]\n");
	}
    }

    ilist_free(created_unit_clauses);
    ilist_free(dead_unit_clauses);
    ilist_free(live_unit_clauses);
    int i;
    /* Free RC table */
    rc_done();
    for (i = 0; i < dfun_count; i++)
	dfuns[i]();
    bdd_report();
    bdd_done();
    prover_done();
    tbdd_report();
}

void tbdd_add_info_fun(tbdd_info_fun f) {
    if (ifun_count >= FUN_MAX) {
	fprintf(ERROUT, "Limit of %d TBDD information functions.  Request ignored\n", FUN_MAX);
	return;
    }
    ifuns[ifun_count++] = f;
}

void tbdd_add_done_fun(tbdd_done_fun f) {
    if (dfun_count >= FUN_MAX) {
	fprintf(ERROUT, "Limit of %d TBDD done functions.  Request ignored\n", FUN_MAX);
	return;
    }
    dfuns[dfun_count++] = f;
}


void tbdd_print(TBDD t, FILE *out) {
    int nid = NNAME(t.root);
    int cid = t.clause_id;
    int rci = t.rc_index;
    int rc = rc_get(rci);
    fprintf(out, "[N%d, Clause #%d, RCI=%d, RC=%d]", nid, cid, rci, rc);
}

TBDD tbdd_create(BDD r, int clause_id) {
    TBDD res;
    //    printf("Adding reference to TBDD %d\n", (int) r);
    res.root = bdd_addref(r);
    res.clause_id = new_unit_clause(clause_id);
    int rci = rc_new_entry(clause_id);
    res.rc_index = rci;
    return res;
}

/* 
   proof_step = TAUTOLOGY
   root = 1
 */
TBDD TBDD_tautology() {
    return tbdd_create(bdd_true(), TAUTOLOGY);
}

/* 
   proof_step = TAUTOLOGY
   root = 0
 */
TBDD TBDD_null() {
    return tbdd_create(bdd_false(), TAUTOLOGY);
}

bool tbdd_is_true(TBDD tr) {
    return ISONE(tr.root);
}

bool tbdd_is_false(TBDD tr) {
    return ISZERO(tr.root);
}

/*
  Increment/decrement reference count for BDD
 */
TBDD tbdd_addref(TBDD tr) {
    bdd_addref(tr.root);
    rc_increment(tr.rc_index);
    return tr;
}

void tbdd_delref(TBDD tr) {
    if (!bddnodes)
	return;
    bdd_delref(tr.root);
    int rc = rc_decrement(tr.rc_index);
    if (rc == 0) {
	int dbuf[1+ILIST_OVHD];
	ilist dlist = ilist_make(dbuf, 1);
	ilist_fill1(dlist, tr.clause_id);
	if (tr.root != bdd_false()) {
	    print_proof_comment(2, "Deleting unit clause #%d for node N%d", tr.clause_id, NNAME(tr.root));
	    delete_clauses(dlist);
	}
	/* Empty clause will be marked as "dead" so that is not later deleted */
	dead_unit_clauses = ilist_push(dead_unit_clauses, tr.clause_id);
	rc_dispose(tr.rc_index);
    }
}

/*
  Make copy of TBDD
 */
static TBDD tbdd_duplicate(TBDD tr) {
    return tbdd_addref(tr);
}

/*
  Generate BDD representation of specified input clause.
  Generate proof that BDD will evaluate to TRUE
  for all assignments satisfying clause.
 */

static TBDD tbdd_from_clause_with_id(ilist clause, int id) {
    print_proof_comment(2, "Build BDD representation of clause #%d", id);
    clause = clean_clause(clause);
    BDD r = BDD_build_clause(clause);
    if (proof_type == PROOF_NONE) {
	return tbdd_create(r, TAUTOLOGY);
    }
    int len = ilist_length(clause);
    int nlits = 2*len+1;
    int abuf[nlits+ILIST_OVHD];
    ilist ant = ilist_make(abuf, nlits);
    /* Clause literals are in descending order */
    ilist_reverse(clause);
    BDD nd = r;
    int i;
    for (i = 0; i < len; i++) {
	int lit = clause[i];
	if (lit < 0) {
	    ilist_push(ant, bdd_dclause(nd, DEF_LU));
	    ilist_push(ant, bdd_dclause(nd, DEF_HU));
	    nd = bdd_high(nd);
	} else {
	    ilist_push(ant, bdd_dclause(nd, DEF_HU));
	    ilist_push(ant, bdd_dclause(nd, DEF_LU));
	    nd = bdd_low(nd);
	}
    } 
    ilist_push(ant, id);
    int cbuf[1+ILIST_OVHD];
    ilist uclause = ilist_make(cbuf, 1);
    ilist_fill1(uclause, XVAR(r));
    print_proof_comment(2, "Validate BDD representation of Clause #%d.  Node = N%d.", id, NNAME(r));
    int clause_id = generate_clause(uclause, ant);
    return tbdd_create(r, clause_id);
}

// This seems like it should be easier to check, but it isn't.
TBDD tbdd_from_clause(ilist clause) {
    int dbuf[ILIST_OVHD+1];
    ilist dels = ilist_make(dbuf, 1);
    int id = assert_clause(clause);
    TBDD tr = tbdd_from_clause_with_id(clause, id);
    delete_clauses(ilist_fill1(dels, id));
    return tr;
}


TBDD tbdd_from_clause_id(int id) {
    ilist clause = get_input_clause(id);
    if (clause == NULL) {
	fprintf(ERROUT, "Invalid input clause #%d\n", id);
	exit(1);
    }
    TBDD tr = tbdd_from_clause_with_id(clause, id);
#if ENABLE_BTRACE
    if (bdd_trace_file)
	fprintf(bdd_trace_file, "tc %d %d\n", tr.root, id);
#endif
    return tr;
}

/*
  For generating xor's: does word have odd or even parity?
*/
static int parity(int w) {
  int odd = 0;
  while (w > 0) {
    odd ^= w & 0x1;
    w >>= 1;
  }
  return odd;
}

/*
  Sort integers in ascending order
 */
int int_compare_tbdd(const void *i1p, const void *i2p) {
  int i1 = *(int *) i1p;
  int i2 = *(int *) i2p;
  if (i1 < i2)
    return -1;
  if (i1 > i2)
    return 1;
  return 0;
}

/*
  Generate BDD for arbitrary-input xor, using
  clauses to ensure that DRAT can validate result
*/

TBDD TBDD_from_xor(ilist vars, int phase) {
    ilist_sort(vars);
    int len = ilist_length(vars);
    int bits;
    int elen = 1 << len;
    int lbuf[ILIST_OVHD+len];
    ilist lits = ilist_make(lbuf, len);
    ilist_resize(lits, len);
    TBDD result = TBDD_tautology();
    for (bits = 0; bits < elen; bits++) {
	int i;
	if (parity(bits) == phase)
	    continue;
	for (i = 0; i < len; i++)
	    lits[i] = (bits >> i) & 0x1 ? -vars[i] : vars[i];
	TBDD tc = tbdd_from_clause(lits);
	if (tbdd_is_true(result)) {
	    result = tc;
	} else {
	    TBDD nresult = tbdd_and(result, tc);
	    tbdd_delref(tc);
	    tbdd_delref(result);
	    result = nresult;
	}
    }
    if (verbosity_level >= 2) {
	ilist_format(vars, ibuf, " ^ ", BUFLEN);
	print_proof_comment(2, "N%d is BDD representation of %s = %d",
			    bdd_nameid(result.root), ibuf, phase);
    }
    return result;
}


/*
  Upgrade ordinary BDD to TBDD by proving
  implication from another TBDD
 */
TBDD tbdd_validate(BDD r, TBDD tr) {
    if (r == tr.root)
	return tbdd_duplicate(tr);
    if (proof_type == PROOF_NONE) {
	return tbdd_create(r, TAUTOLOGY);
    }
    int cbuf[1+ILIST_OVHD];
    ilist clause = ilist_make(cbuf, 1);
    int abuf[2+ILIST_OVHD];
    ilist ant = ilist_make(abuf, 2);
    pcbdd p = bdd_imptst_justify(tr.root, r);
    if (p.root != bdd_true()) {
	fprintf(ERROUT, "Failed to prove implication N%d --> N%d\n", NNAME(tr.root), NNAME(r));
	exit(1);
    }
    print_proof_comment(2, "Validation of unit clause for N%d by implication from N%d",NNAME(r), NNAME(tr.root));
    ilist_fill1(clause, XVAR(r));
    ilist_fill2(ant, p.clause_id, tr.clause_id);
    int clause_id = generate_clause(clause, ant);
#if ENABLE_BTRACE
    if (bdd_trace_file)
	fprintf(bdd_trace_file, "ti %d %d\n", r, tr.root);
#endif
    /* Now we can handle any deletions caused by GC */
    process_deferred_deletions();
    return tbdd_create(r, clause_id);
}

/*
  Declare BDD to be trustworthy.  Proof
  checker must provide validation.
  Only works when generating DRAT proofs
 */
TBDD TBDD_trust(BDD r) {
    //    printf("Trying to trust BDD %d.  proof_type = %d\n", (int) r, proof_type);
    if (proof_type == PROOF_NONE) {
	//	printf("Calling tbdd_create\n");
	return tbdd_create(r, TAUTOLOGY);
    }
    int cbuf[1+ILIST_OVHD];
    ilist clause = ilist_make(cbuf, 1);
    int abuf[0+ILIST_OVHD];
    ilist ant = ilist_make(abuf, 0);
    print_proof_comment(2, "Assertion of N%d",NNAME(r));
    ilist_fill1(clause, XVAR(r));
    int clause_id = generate_clause(clause, ant);
    return tbdd_create(r, clause_id);
}

/*
  Form conjunction of two TBDDs and prove
  their conjunction implies the new one
 */
TBDD tbdd_and(TBDD tr1, TBDD tr2) {
    if (proof_type == PROOF_NONE) {
	BDD r = bdd_and(tr1.root, tr2.root);
	return tbdd_create(r, TAUTOLOGY);
    }
    if (tbdd_is_true(tr1))
	return tbdd_duplicate(tr2);
    if (tbdd_is_true(tr2))
	return tbdd_duplicate(tr1);
    pcbdd p = bdd_and_justify(tr1.root, tr2.root);
    BDD r = p.root;
    int cbuf[1+ILIST_OVHD];
    ilist clause = ilist_make(cbuf, 1);
    int abuf[3+ILIST_OVHD];
    ilist ant = ilist_make(abuf, 3);
    if (r == bdd_false())
	print_proof_comment(2, "Validate empty clause for node N%d = N%d & N%d", NNAME(r), NNAME(tr1.root), NNAME(tr2.root));
    else
	print_proof_comment(2, "Validate unit clause for node N%d = N%d & N%d", NNAME(r), NNAME(tr1.root), NNAME(tr2.root));
    ilist_fill1(clause, XVAR(r));
    ilist_fill3(ant, tr1.clause_id, tr2.clause_id, p.clause_id);
    /* Insert proof of unit clause into t's justification */
    int clause_id = generate_clause(clause, ant);
#if ENABLE_BTRACE
    if (bdd_trace_file)
	fprintf(bdd_trace_file, "ta %d %d %d\n", r, tr1.root, tr2.root);
#endif
    /* Now we can handle any deletions caused by GC */
    process_deferred_deletions();
    return tbdd_create(r, clause_id);
}

/*
  Form conjunction of TBDDs tr1 & tr2.  Use to validate
  BDD r
 */
TBDD tbdd_validate_with_and(BDD r, TBDD tr1, TBDD tr2) {
    if (proof_type == PROOF_NONE)
	return TBDD_trust(r);
    if (tbdd_is_true(tr1))
	return tbdd_validate(r, tr2);
    if (tbdd_is_true(tr2))
	return tbdd_validate(r, tr1);
    pcbdd p = bdd_and_imptst_justify(tr1.root, tr2.root, r);
    if (p.root != bdd_true()) {
	fprintf(ERROUT, "Failed to prove implication N%d & N%d --> N%d\n", NNAME(tr1.root), NNAME(tr2.root), NNAME(r));
	exit(1);
    }
    int cbuf[1+ILIST_OVHD];
    ilist clause = ilist_make(cbuf, 1);
    int abuf[3+ILIST_OVHD];
    ilist ant = ilist_make(abuf, 3);
    print_proof_comment(2, "Validate unit clause for node N%d, based on N%d & N%d", NNAME(r), NNAME(tr1.root), NNAME(tr2.root));
    ilist_fill1(clause, XVAR(r));
    ilist_fill3(ant, tr1.clause_id, tr2.clause_id, p.clause_id);
    /* Insert proof of unit clause into rr's justification */
    int clause_id = generate_clause(clause, ant);
    /* Now we can handle any deletions caused by GC */
    process_deferred_deletions();
    return tbdd_create(r, clause_id);
}

/*
  Validate that a clause is implied by a TBDD.
  Use this version when generating LRAT proofs
  Returns clause id.
 */

/* See if can validate clause directly from path in BDD */

static bool test_validation_path(ilist clause, TBDD tr) {
    // Put in descending order by level
    clause = clean_clause(clause);
    int len = ilist_length(clause);
    int i;
    BDD r = tr.root;
    for (i = len-1; i >= 0; i--) {
	int lit = clause[i];
	int var = ABS(lit);
	int level = bdd_var2level(var);
	if (LEVEL(r) > level)
	    // Function does not depend on this variable
	    continue;
	if (LEVEL(r) < level)
	    // Cannot validate clause directly
	    return false;
	if (lit < 0)
	    r = HIGH(r);
	else
	    r = LOW(r);
    }
    return ISZERO(r);
}

static int tbdd_validate_clause_path(ilist clause, TBDD tr) {
    int len = ilist_length(clause);
    int abuf[1+len+ILIST_OVHD];
    int i;
    BDD r = tr.root;
    ilist ant = ilist_make(abuf, 1+len);
    ilist_fill1(ant, tr.clause_id);
    for (i = len-1; i >= 0; i--) {
	int lit = clause[i];
	int var = ABS(lit);
	int id;
	if (LEVEL(r) > var)
	    // Function does not depend on this variable
	    continue;
	if (LEVEL(r) < var)
	    // Cannot validate clause directly
	    return -1;
	if (lit < 0) {
	    id = bdd_dclause(r, DEF_HD);
	    r = HIGH(r);
	} else {
	    id = bdd_dclause(r, DEF_LD);
	    r = LOW(r);
	}
	if (id != TAUTOLOGY)
	    ilist_push(ant, id);
    }
    if (verbosity_level >= 2) {
	char buf[BUFLEN];
	ilist_format(clause, buf, " ", BUFLEN);
	print_proof_comment(2, "Validation of clause [%s] from N%d", buf, NNAME(tr.root));
    }
    int id =  generate_clause(clause, ant);
    return id;
}

int tbdd_validate_clause(ilist clause, TBDD tr) {
    if (proof_type == PROOF_NONE)
	return TAUTOLOGY;
    clause = clean_clause(clause);
    if (test_validation_path(clause, tr)) {
	return tbdd_validate_clause_path(clause, tr);
    } else {
	if (verbosity_level >= 2) {
	    char buf[BUFLEN];
	    ilist_format(clause, buf, " ", BUFLEN);
	    print_proof_comment(2, "Validation of clause [%s] from N%d requires generating intermediate BDD", buf, NNAME(tr.root));
	}
	BDD cr = BDD_build_clause(clause);
	bdd_addref(cr);
	TBDD tcr = tbdd_validate(cr, tr);
	bdd_delref(cr);
	int id = tbdd_validate_clause_path(clause, tcr);
	if (id < 0) {
	    char buf[BUFLEN];
	    ilist_format(clause, buf, " ", BUFLEN);
	    print_proof_comment(2, "Oops.  Couldn't validate clause [%s] from N%d", buf, NNAME(tr.root));
	}
	tbdd_delref(tcr);
	return id;
    }
}

/*
  Assert that a clause holds.  Proof checker
  must provide validation.
  Use this version when generating DRAT proofs,
  or when don't want to provide antecedent in FRAT proof
  Returns clause id.
 */
int assert_clause(ilist clause) {
    if (proof_type == PROOF_NONE)
	return TAUTOLOGY;
    int abuf[1+ILIST_OVHD];
    ilist ant = ilist_make(abuf, 1);
    if (verbosity_level >= 2) {
	char buf[BUFLEN];
	ilist_format(clause, buf, " ", BUFLEN);
	print_proof_comment(2, "Assertion of clause [%s]", buf);
    }
    return generate_clause(clause, ant);
}

/*============================================
 Useful BDD operations
============================================*/

/*
  Build BDD representation of XOR (phase = 1) or XNOR (phase = 0)
*/
BDD BDD_build_xor(ilist vars, int phase) {
    if (ilist_length(vars) == 0)
	return phase ? bdd_false() : bdd_true();
    ilist variables = ilist_copy(vars);
    /* Put into descending order by level */
    variables = clean_clause(variables);
    int n = ilist_length(variables);
    BDD even = bdd_addref(bdd_true());
    BDD odd = bdd_addref(bdd_false());
    int i, var, level;
    //    printf("Building Xor for [");
    //    ilist_print(variables, stdout, " ");
    //    printf("]\n");

    for (i = 0; i < n-1; i++) {
	var = variables[i];
	level = bdd_var2level(var);
	BDD neven = bdd_addref(bdd_makenode(level, even, odd));
	BDD nodd = bdd_addref(bdd_makenode(level, odd, even));
	bdd_delref(even);
	bdd_delref(odd);
	even = neven;
	odd = nodd;
    }
    var = variables[n-1];
    level = bdd_var2level(var);
    BDD r = phase ? bdd_makenode(level, odd, even) : bdd_makenode(level, even, odd);
    bdd_delref(even);
    bdd_delref(odd);
    ilist_free(variables);
    return r;
}

/*
  Build BDD representation of clause.
 */
BDD BDD_build_clause(ilist literals) {
    /* Put into descending order by level */
    literals = clean_clause(literals);
    if (literals == TAUTOLOGY_CLAUSE)
	return bdd_true();
    BDD r = bdd_false();
    int i, lit, var, level;
    for (i = 0; i < ilist_length(literals); i++) {
	bdd_addref(r);
	lit = literals[i];
	var = ABS(lit);
	level = bdd_var2level(var);
	BDD nr = lit < 0 ? bdd_makenode(level, bdd_true(), r) : bdd_makenode(level, r, bdd_true());
	bdd_delref(r);
	r = nr;
    }
    return r;
}

/*
  Build BDD representation of conjunction of literals (a "cube")
 */
BDD BDD_build_cube(ilist literals) {
    if (literals == FALSE_CUBE)
	return bdd_false();
    /* Put into descending order by level */
    literals = clean_clause(literals);
    BDD r = bdd_true();
    int i, lit, var, level;
    for (i = 0; i < ilist_length(literals); i++) {
	bdd_addref(r);
	lit = literals[i];
	var = ABS(lit);
	level = bdd_var2level(var);
	BDD nr = lit < 0 ? bdd_makenode(level, r, bdd_false()) : bdd_makenode(level, bdd_false(), r);
	bdd_delref(r);
	r = nr;
    }
    return r;
}

ilist BDD_decode_cube(BDD r) {
    ilist literals = ilist_new(1);
    if (r == bdd_false())
	return FALSE_CUBE;
    while (r != bdd_true()) {
	int var = bdd_var(r);
	if (bdd_high(r) == bdd_false()) {
	    literals = ilist_push(literals, -var);
	    r = bdd_low(r);
	} else {
	    literals = ilist_push(literals, var);
	    r = bdd_high(r);
	}
    }
    return literals;

}
