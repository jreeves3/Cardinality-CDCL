#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Returns the positive number '1' ( > 0) if the given clause is root level
// satisfied or the negative number '-1' ( < 0) if it is not root level
// satisfied but contains a root level falsified literal. Otherwise, if it
// contains neither a satisfied nor falsified literal, then '0' is returned.

int Internal::clause_contains_fixed_literal (Clause * c) {
  int satisfied = 0, falsified = 0;
  for (const auto & lit : *c) {
    const int tmp = fixed (lit);
    if (tmp > 0) {
      LOG (c, "root level satisfied literal %d in", lit);
      satisfied++;
    }
    if (tmp < 0) {
      LOG (c, "root level falsified literal %d in", lit);
      falsified++;
    }
  }
       if (satisfied) return 1;
  else if (falsified) return -1;
  else                return 0;
}

// if tmp > 0, clause is satisfied
// if tmp = 0, no change
// if tmp < 0, remove satisfied or falsified literals
int Internal::CARclause_contains_fixed_literal (Clause * c) {
  int satisfied = 0, falsified = 0;
  int bound = c->CARbound ();
  for (const auto & lit : *c) {
    const int tmp = fixed (lit);
    if (tmp > 0) {
      LOG (c, "root level satisfied literal %d in", lit);
      satisfied++;
    }
    if (tmp < 0) {
      LOG (c, "root level falsified literal %d in", lit);
      falsified++;
    }
  }
  if (c->guard_literal) {
    const int tmp = fixed (c->guard_literal);
    if (tmp > 0) satisfied = bound;
    if (tmp < 0) falsified++;
  }
       if (satisfied >= bound) return 1;
  else if (falsified || satisfied) return -1;
  else                return 0;
}

// Assume that the clause is not root level satisfied but contains a literal
// set to false (root level falsified literal), so it can be shrunken.  The
// clause data is not actually reallocated at this point to avoid dealing
// with issues of special policies for watching binary clauses or whether a
// clause is extended or not. Only its size field is adjusted accordingly
// after flushing out root level falsified literals.

void Internal::remove_falsified_literals (Clause * c) {
  const const_literal_iterator end = c->end ();
  const_literal_iterator i;
  int num_non_false = 0;
  for (i = c->begin (); num_non_false < 2 && i != end; i++)
    if (fixed (*i) >= 0) num_non_false++;
  if (num_non_false < 2) return;
  if (proof) proof->flush_clause (c);
  literal_iterator j = c->begin ();
  for (i = j; i != end; i++) {
    const int lit = *j++ = *i, tmp = fixed (lit);
    assert (tmp <= 0);
    if (tmp >= 0) continue;
    LOG ("flushing %d", lit);
    j--;
  }
  stats.collected += shrink_clause (c, j - c->begin ());
}

// Helper function to swap a literal in a cardinality constraint
inline void Internal::CARswap_watched_literal (Clause *c, const int lit, int lit_pos) {
  literal_iterator lits = c->begin ();

  const int unwatched = c->CARbound () + 1; // new bound

  const int size = c->size;
  const literal_iterator middle = lits + c->pos;
  const const_literal_iterator end = lits + size;
  literal_iterator k = middle;

  assert (c->pos >= unwatched && c->pos <= size); 
  // if (c->pos >= size) {
  //   int satisfied = 0, falsified = 0;
  //   int bound = c->CARbound ();
  //   for (const auto & lit : *c) {
  //     const int tmp = fixed (lit);
  //     if (tmp > 0) {
  //       LOG (c, "root level satisfied literal %d in", lit);
  //       satisfied++;
  //     }
  //     if (tmp < 0) {
  //       LOG (c, "root level falsified literal %d in", lit);
  //       falsified++;
  //     }
  //   }
  //   printf("bound %d, nsat %d, nunsat %d, size %d, pos %d, unwatched %d \n", bound, satisfied, falsified, size, c->pos, c->unwatched);

  //   c->pos = unwatched; 
  // }
  //TODO this shouldn't happen...
  //It just means you are at the end
  //not possible because it always resets...
  // possible if coming in fresh (all watched) then some var is sat
  // assert (c->pos < size);

  // Find replacement watch 'r' at position 'k' with value 'v'.

  int r = 0;
  int v = 0;

  int failed = 1;

  r = *k;
  while (k != end && (!(v = !fixed (r)) || val (r) < 0)) { // must be unassigned at top_level
    k++;
    r = *k;
  }

  

  if (!v || k == end) {  // need second search starting at the head?

    k = lits + unwatched;
    r = *k;
    while (k != middle && (!(v = !fixed (r)) || val (r) < 0)) {
      k++;
      r = *k;
    }
    if (k != middle) failed = 0;
  } else failed = 0;

  assert (lits [lit_pos] == lit);
  

  

  // if (c->pos >= size) {
  //   for (int i = 0; i < c->size; i++) {
  //     printf ("lit %d val %d\n", lits[i], val (lits[i]));
  //   }
  //   printf ("bound %d\n", unwatched-1);
  // }
  if (failed) { // currently in conflict, relax swap conditions
    k = lits + unwatched;
    r = *k;
    while (k != end && (!(v = !fixed (r)))) {
      // if (lit == -175480)
      //   printf("lit %d\n",r);
      k++;
      r = *k;
    }
  }

  c->pos = k - lits;  // always save position

  
  assert (lits[c->pos] == r);

  assert (k <= c->end ());

  // if (!v || !(c->pos >= unwatched && c->pos < size)) {
  //   for (int i = 0; i < c->size; i++) {
  //     printf ("lit %d val %d fixed %d\n", lits[i], val (lits[i]), fixed (lits[i]));
  //   }
  //   printf ("bound %d cpos %d\n", unwatched-1, c->pos);
  //   printf ("Swapping %d\n", lit);
  // }

  assert (c->pos >= unwatched && c->pos < size);
  assert (v); // Replacement satisfied or unassigned, simple swap
  // assert (val (r) >= 0);

  // swap position
  lits[lit_pos] = r;
  *k = lit;
  // printf ("%d at pos %d",r, lit_pos);
  // printf ("%d at pos %d",lit, c->pos);

  assert ((k-lits) >= unwatched);
  // if ((k-lits) < unwatched) { // currently watched but at wrong position watched
  //   if (CARwatch_in_garbage)
  //     remove_watch (watches (r), c); // Drop this watch from the watch list of 'lit'.
  // }  // could simply update the watch pos, then have an else with CARwatch_literal
    
  if (CARwatch_in_garbage && opts.ccdclMode != 2) {
    // printf("unwwatch %d\n",lit);
    remove_watch (watches (lit), c); // Drop this watch from the watch list of 'lit'.
  // watch new literal at position my_lit_pos
    // printf("wwatch %d\n",r);
    CARwatch_literal (r, lit_pos, c);
  }

  LOG (c, "unwatch %d in", lit);
}

// Assume the cardinality constraint is not root level satisfied but 
// contains root level satisfied or falsified literals.
// For satisfied literals, we must adjust the bound.
// Need to check if a watched literal is satisfied
void Internal::CARremove_falsified_and_satisfied_literals (Clause * c) {
  const const_literal_iterator end = c->end ();
  const_literal_iterator i;
  int num_non_false = 0;
  int num_true = 0;
  int new_bound;
  int old_bound = c->CARbound ();
  for (i = c->begin ();i != end; i++) {
    if (! fixed (*i)) num_non_false++;
    if (fixed (*i) > 0) num_true++;
  }
  new_bound = old_bound - num_true;

  assert (num_non_false >= 2);

  // if (new_bound == 1) { // add as a clause
  //   printf ("adding with size %d, watch %d\n", num_non_false, CARwatch_in_garbage);
  //   if (CARwatch_in_garbage)
  //     CARunwatch_some_literals (c, 0); // unwatch all literals
  //   clause.clear ();
  //   for (i = c->begin ();i != end; i++) {
  //     if (!fixed (*i))
  //       clause.push_back (*i);
  //   }
  //   Clause * d = new_clause (c->redundant);
  //   clause.clear(); // need to clear before proof logging
  //   if (proof) {
  //       proof->add_derived_clause (d);
  //       clause.clear(); }
  //   if (CARwatch_in_garbage)
  //     watch_clause (d);
  //   CARmark_garbage (c);
  //   return;
  // }

  assert (new_bound > 0);
  assert (num_non_false > new_bound);
  assert (num_non_false != new_bound);
  if (num_non_false == new_bound) return; // unit (is this possible? block with assertion)
  if (num_true) {// new bound decremented by number true literals
    // printf("unwwatch all\n");
    if (CARwatch_in_garbage && opts.ccdclMode != 2)
      CARunwatch_some_literals (c, new_bound); // unwatch literals no longer needed
    if (c->unwatched == c->size+1) {
      if (CARwatch_in_garbage) remove_watch (watches (c->literals[new_bound]), c);
      c->unwatched = new_bound; // assume no falsified constraints or this would already be in conflict
    } else
      c->unwatched = new_bound + 1; // update unwatched with new bound
  }
  // if (proof) proof->flush_clause (c); // no proof for cardinality constraints
  // literal_iterator j = c->begin ();
  int early_it = 0;
  for (int lit_pos = 0; lit_pos < c->size; lit_pos++) {
    // printf("%d\n",lit_pos);
  //   if (CARwatch_in_garbage) {
  //   CARunwatch_some_literals (c, -1);
  //   CARwatch_clause (c, new_bound);
  // }
    const int lit = c->literals[lit_pos], tmp = fixed (lit);
    if (!tmp) {c->literals[early_it++] = lit; continue;} // unassigned literal is kept in constraint
    if (tmp && lit_pos < new_bound + 1) { // remove satisfied literal
      LOG ("flushing and swapping literal %d", lit);
      CARswap_watched_literal (c, lit, lit_pos);
      // c->literals[early_it++] = lit;
      early_it++;
      continue;
    }
    LOG ("flushing literal %d", lit);
  }

  // Promoted to normal cardinality constraint if guard = 0
  if (CARwatch_in_garbage && c->guard_literal && fixed (c->guard_literal) < 0) {
    // printf("Guard %d\n",c->guard_literal);
    remove_watch (watches (c->guard_literal), c); 
    c->guard_literal = 0;
  }

  // may have just been guard satisfied, at which point we don't shrink
  if (early_it < c->size)
    stats.collected += shrink_clause (c, early_it);

  // if (CARwatch_in_garbage) {
  //   CARunwatch_some_literals (c, -1);
  //   CARwatch_clause (c, new_bound);
  // }

}

// If there are new units (fixed variables) since the last garbage
// collection we go over all clauses, mark satisfied ones as garbage and
// flush falsified literals.  Otherwise if no new units have been generated
// since the last garbage collection just skip this step.

void Internal::mark_satisfied_clauses_as_garbage () {

  // if (!CARwatch_in_garbage) assert (! watching ());

  if (last.collect.fixed >= stats.all.fixed) return;
  last.collect.fixed = stats.all.fixed;

  LOG ("marking satisfied clauses and removing falsified literals");

  for (const auto & c : clauses) {
    if (c->garbage) continue;
    const int tmp = clause_contains_fixed_literal (c);
         if (tmp > 0) mark_garbage (c);
    else if (tmp < 0) remove_falsified_literals (c);
  }

  LOG ("marking satisfied card constraints and removing falsified literals");

  for (const auto & c : CARclauses) {
    if (c->garbage) continue;
    const int tmp = CARclause_contains_fixed_literal (c);
         if (tmp > 0) CARmark_garbage (c); // removed in garbage collection
    else if (tmp < 0) CARremove_falsified_and_satisfied_literals (c);
  }

}

/*------------------------------------------------------------------------*/

// Reason clauses can not be collected.
//
// We protect reasons before and release protection after garbage collection
// (actually within garbage collection).
//
// For 'reduce' we still need to make sure that all clauses which should not
// be removed are marked as such and thus we need to call it before marking
// clauses to be flushed.

void Internal::protect_reasons () {
  LOG ("protecting reason clauses of all assigned variables on trail");
  assert (!protected_reasons);
  size_t count = 0;
  for (const auto & lit : trail) {
    if (!active (lit)) continue;
    assert (val (lit));
    Var & v = var (lit);
    assert (v.level > 0);
    Clause * reason = v.reason;
    if (!reason) continue;
    LOG (reason, "protecting assigned %d reason %p", lit, (void*) reason);
    // assert (!reason->reason);
    reason->reason = true;
    count++;
  }
  LOG ("protected %zd reason clauses referenced on trail", count);
  protected_reasons = true;
}

/*------------------------------------------------------------------------*/

// After garbage collection we reset the 'reason' flag of the reasons
// of assigned literals on the trail.

void Internal::unprotect_reasons () {
  LOG ("unprotecting reasons clauses of all assigned variables on trail");
  assert (protected_reasons);
  size_t count = 0;
  for (const auto & lit : trail) {
    if (!active (lit)) continue;
    assert (val (lit));
    Var & v = var (lit);
    assert (v.level > 0);
    Clause * reason = v.reason;
    if (!reason) continue;
    LOG (reason, "unprotecting assigned %d reason %p", lit, (void*) reason);
    // assert (reason->reason);
    reason->reason = false;
    count++;
  }
  LOG ("unprotected %zd reason clauses referenced on trail", count);
  protected_reasons = false;
}

/*------------------------------------------------------------------------*/

// Update occurrence lists before deleting garbage clauses in the context of
// preprocessing, e.g., during bounded variable elimination 'elim'.  The
// result is the number of remaining clauses, which in this context means
// the number of non-garbage clauses.

size_t Internal::flush_occs (int lit) {
  Occs & os = occs (lit);
  const const_occs_iterator end = os.end ();
  occs_iterator j = os.begin ();
  const_occs_iterator i;
  size_t res = 0;
  Clause * c;
  for (i = j; i != end; i++) {
    c = *i;
    if (c->collect ()) continue;
    *j++ = c->moved ? c->copy : c;
    assert (!c->redundant);
    res++;
  }
  os.resize (j - os.begin ());
  shrink_occs (os);
  return res;
}

// Update watch lists before deleting garbage clauses in the context of
// 'reduce' where we watch and no occurrence lists.  We have to protect
// reason clauses not be collected and thus we have this additional check
// hidden in 'Clause.collect', which for the root level context of
// preprocessing is actually redundant.

inline void Internal::flush_watches (int lit, Watches & saved) {
  assert (saved.empty ());
  Watches & ws = watches (lit);
  const const_watch_iterator end = ws.end ();
  watch_iterator j = ws.begin ();
  const_watch_iterator i;
  for (i = j; i != end; i++) {
    Watch w = *i;
    Clause * c = w.clause;
    if (c->collect ()) continue;
    if (c->moved) c = w.clause = c->copy;
    w.size = c->size;
    if (!w.cardinality_clause()) {
      const int new_blit_pos = (c->literals[0] == lit);
      assert (c->literals[!new_blit_pos] == lit);        /*FW1*/
      w.set_blit(c->literals[new_blit_pos]);
    }
    if (w.binary ()) *j++ = w;
    else saved.push_back (w);
  }
  ws.resize (j - ws.begin ());
  for (const auto & w : saved) ws.push_back (w);
  saved.clear ();
  shrink_vector (ws);
}

void Internal::flush_all_occs_and_watches () {
  if (occurring ())
    for (auto idx : vars)
      flush_occs (idx), flush_occs (-idx);

  if (watching ()) {
    Watches tmp;
    for (auto idx : vars)
      flush_watches (idx, tmp), flush_watches (-idx, tmp);
  }
}

/*------------------------------------------------------------------------*/

void Internal::update_reason_references () {
  LOG ("update assigned reason references");
  size_t count = 0;
  for (auto & lit : trail) {
    if (!active (lit)) continue;
    Var & v = var (lit);
    Clause * c = v.reason;
    if (!c) continue;
    if (c->unwatched > 2) continue; // CAR check
    if (c->encoding) continue;
    LOG (c, "updating assigned %d reason", lit);
    assert (c->reason);
    assert (c->moved);
    Clause * d = c->copy;
    v.reason = d;
    count++;
  }
  LOG ("updated %zd assigned reason references", count);
}

/*------------------------------------------------------------------------*/

// This is a simple garbage collector which does not move clauses.  It needs
// less space than the arena based clause allocator, but is not as cache
// efficient, since the copying garbage collector can put clauses together
// which are likely accessed after each other.

void Internal::delete_garbage_clauses () {

  flush_all_occs_and_watches ();

  LOG ("deleting garbage clauses");
  int64_t collected_bytes = 0, collected_clauses = 0;
  const auto end = clauses.end ();
  auto j = clauses.begin (), i = j;
  while (i != end) {
    Clause * c = *j++ = *i++;
    if (!c->collect ()) continue;
    collected_bytes += c->bytes ();
    collected_clauses++;
    delete_clause (c);
    j--;
  }
  clauses.resize (j - clauses.begin ());
  shrink_vector (clauses);

  PHASE ("collect", stats.collections,
    "collected %" PRId64 " bytes of %" PRId64 " garbage clauses",
    collected_bytes, collected_clauses);
}

// same as above but for cardinality constraints
void Internal::CARdelete_garbage_clauses () {

  // flush_all_occs_and_watches ();

  LOG ("deleting garbage cardinality constraints");
  int64_t collected_bytes = 0, collected_clauses = 0;
  const auto end = CARclauses.end ();
  auto j = CARclauses.begin (), i = j;
  while (i != end) {
    Clause * c = *j++ = *i++;
    if (!c->collect ()) continue;
    collected_bytes += c->bytes ();
    collected_clauses++;
    CARdelete_clause (c); // can't delete this in proof
    j--;
  }
  CARclauses.resize (j - CARclauses.begin ());
  shrink_vector (CARclauses);

  PHASE ("collect", stats.collections,
    "collected %" PRId64 " bytes of %" PRId64 " garbage clauses",
    collected_bytes, collected_clauses);
}

/*------------------------------------------------------------------------*/

// This is the start of the copying garbage collector using the arena.  At
// the core is the following function, which copies a clause to the 'to'
// space of the arena.  Be careful if this clause is a reason of an
// assignment.  In that case update the reason reference.
//
void Internal::copy_clause (Clause * c) {
  LOG (c, "moving");
  assert (!c->moved);
  char * p = (char*) c;
  char * q = arena.copy (p, c->bytes ());
  c->copy = (Clause *) q;
  c->moved = true;
  LOG ("copied clause[%" PRId64 "] from %p to %p",
       c->id, (void*) c, (void*) c->copy);
}

// This is the moving garbage collector.

void Internal::copy_non_garbage_clauses () {

  size_t collected_clauses = 0, collected_bytes = 0;
  size_t     moved_clauses = 0,     moved_bytes = 0;

  // First determine 'moved_bytes' and 'collected_bytes'.
  //
  for (const auto & c : clauses)
    if (!c->collect ()) moved_bytes += c->bytes (), moved_clauses++;
    else collected_bytes += c->bytes (), collected_clauses++;

  PHASE ("collect", stats.collections,
    "moving %zd bytes %.0f%% of %zd non garbage clauses",
    moved_bytes,
    percent (moved_bytes, collected_bytes + moved_bytes),
    moved_clauses);

  // Prepare 'to' space of size 'moved_bytes'.
  //
  arena.prepare (moved_bytes);

  // Keep clauses in arena in the same order.
  //
  if (opts.arenacompact)
    for (const auto & c : clauses)
      if (!c->collect () && arena.contains (c))
        copy_clause (c);

  if (opts.arenatype == 1 || !watching ()) {

    // Localize according to current clause order.

    // If the option 'opts.arenatype == 1' is set, then this means the
    // solver uses the original order of clauses.  If there are no watches,
    // we can not use the watched based copying policies below.  This
    // happens if garbage collection is triggered during bounded variable
    // elimination.

    // Copy clauses according to the order of calling 'copy_clause', which
    // in essence just gives a compacting garbage collector, since their
    // relative order is kept, and actually already gives the largest
    // benefit due to better cache locality.

    for (const auto & c : clauses)
      if (!c->moved && !c->collect ())
        copy_clause (c);

  } else if (opts.arenatype == 2) {

    // Localize according to (original) variable order.

    // This is almost the version used by MiniSAT and descendants.
    // Our version uses saved phases too.

    for (int sign = -1; sign <= 1; sign += 2)
      for (auto idx : vars)
        for (const auto & w : watches (sign * likely_phase (idx)))
          if (!w.clause->moved && !w.clause->collect ())
            copy_clause (w.clause);

  } else {

    // Localize according to decision queue order.

    // This is the default for search. It allocates clauses in the order of
    // the decision queue and also uses saved phases.  It seems faster than
    // the MiniSAT version and thus we keep 'opts.arenatype == 3'.

    assert (opts.arenatype == 3);

    for (int sign = -1; sign <= 1; sign += 2)
      for (int idx = queue.last; idx; idx = link (idx).prev)
        for (const auto & w : watches (sign * likely_phase (idx)))
          if (!w.clause->moved && !w.clause->collect () && !w.cardinality_clause() && !w.clause->encoding)
            copy_clause (w.clause);
  }

  // Do not forget to move clauses which are not watched, which happened in
  // a rare situation, and now is only left as defensive code.
  //
  for (const auto & c : clauses)
    if (!c->collect () && !c->moved)
      copy_clause (c);

  flush_all_occs_and_watches ();
  update_reason_references ();

  // Replace and flush clause references in 'clauses'.
  //
  const auto end = clauses.end ();
  auto j = clauses.begin (), i = j;
  for (; i != end; i++) {
    Clause * c = *i;
    if (c->collect ()) delete_clause (c);
    else assert (c->moved), *j++ = c->copy, deallocate_clause (c);
  }
  clauses.resize (j - clauses.begin ());
  if (clauses.size () < clauses.capacity ()/2) shrink_vector (clauses);

  if (opts.arenasort)
    rsort (clauses.begin (), clauses.end (), pointer_rank ());

  // Release 'from' space completely and then swap 'to' with 'from'.
  //
  arena.swap ();

  PHASE ("collect", stats.collections,
    "collected %zd bytes %.0f%% of %zd garbage clauses",
    collected_bytes,
    percent (collected_bytes, collected_bytes + moved_bytes),
    collected_clauses);
}

/*------------------------------------------------------------------------*/

// Maintaining clause statistics is complex and error prone but necessary
// for proper scheduling of garbage collection, particularly during bounded
// variable elimination.  With this function we can check whether these
// statistics are updated correctly.

void Internal::check_clause_stats () {
#ifndef NDEBUG
  int64_t irredundant = 0, redundant = 0, total = 0, irrbytes = 0;
  for (const auto & c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) redundant++; else irredundant++;
    if (!c->redundant) irrbytes += c->bytes ();
    total++;
  }
  for (const auto & c : CARclauses) {
    if (c->garbage) continue;
    if (c->redundant) redundant++; else irredundant++;
    if (!c->redundant) irrbytes += c->bytes ();
    total++;
  }
  for (const auto & c : CARencodingClauses) {
    if (c->garbage) continue;
    if (c->redundant) redundant++; else irredundant++;
    if (!c->redundant) irrbytes += c->bytes ();
    total++;
  }


  assert (stats.current.irredundant == irredundant);
  assert (stats.current.redundant == redundant);
  assert (stats.current.total == total);
  assert (stats.irrbytes == irrbytes);
#endif
}

/*------------------------------------------------------------------------*/

bool Internal::arenaing () {
  return opts.arena && (stats.collections > 1);
}

void Internal::garbage_collection () {
  if (unsat) return;
  START (collect);
  report ('G', 1);
  stats.collections++;
  mark_satisfied_clauses_as_garbage ();
  if (!protected_reasons) protect_reasons ();
  if (arenaing ()) copy_non_garbage_clauses ();
  else {
    delete_garbage_clauses ();
    CARdelete_garbage_clauses ();
  }
  check_clause_stats ();
  check_var_stats ();
  unprotect_reasons ();
  report ('C', 1);
  STOP (collect);
  // if (CARwatch_in_garbage) {
  //   clear_watches ();
  //   connect_watches ();
  // }
}

}
