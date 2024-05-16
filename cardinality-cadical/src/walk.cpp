#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Random walk local search based on 'ProbSAT' ideas.

struct Walker {

  Internal * internal;

  Random random;                // local random number generator
  int64_t propagations;         // number of propagations
  int64_t limit;                // limit on number of propagations
  vector <Clause *> broken;     // currently unsatisfied clauses
  double epsilon;               // smallest considered score
  vector<double> table;         // break value to score table
  vector<double> scores;        // scores of candidate literals

  vector <Clause *> broken_card; // currently unsatisfied cardinality constraints
  int constraint_selection;      // (0) weighted random, (1) card first, (2) cls first
  int card_wt_rule;              // weight rule for cardinality constraints

  double score (unsigned);      // compute score from break count

  Walker (Internal *, double size, int64_t limit);
};

// These are in essence the CB values from Adrian Balint's thesis.  They
// denote the inverse 'cb' of the base 'b' of the (probability) weight
// 'b^-i' for picking a literal with the break value 'i' (first column is
// the 'size', second the 'CB' value).

static double cbvals[][2] = {
  { 0.0, 2.00 },
  { 3.0, 2.50 },
  { 4.0, 2.85 },
  { 5.0, 3.70 },
  { 6.0, 5.10 },
  { 7.0, 7.40 },        // Adrian has '5.4', but '7.4' looks better.
};

static const int ncbvals = sizeof cbvals / sizeof cbvals[0];

// We interpolate the CB values for uniform random SAT formula to the non
// integer situation of average clause size by piecewise linear functions.
//
//   y2 - y1
//   ------- * (x - x1) + y1
//   x2 - x1
//
// where 'x' is the average size of clauses and 'y' the CB value.

inline static double fitcbval (double size) {
  int i = 0;
  while (i+2 < ncbvals && (cbvals[i][0] > size || cbvals[i+1][0] < size))
    i++;
  const double x2 = cbvals[i+1][0], x1 = cbvals[i][0];
  const double y2 = cbvals[i+1][1], y1 = cbvals[i][1];
  const double dx = x2 - x1, dy = y2 - y1;
  assert (dx);
  const double res = dy * (size - x1) / dx + y1;
  assert (res > 0);
  return res;
}

// Initialize the data structures for one local search round.

Walker::Walker (Internal * i, double size, int64_t l) :
  internal (i),
  random (internal->opts.seed),         // global random seed
  propagations (0),
  limit (l)
{
  random += internal->stats.walk.count; // different seed every time

  constraint_selection = i->opts.ccdclWalkSelect;
  card_wt_rule = i->opts.ccdclWalkWtRule;

  // This is the magic constant in ProbSAT (also called 'CB'), which we pick
  // according to the average size every second invocation and otherwise
  // just the default '2.0', which turns into the base '0.5'.
  //
  const bool use_size_based_cb = (internal->stats.walk.count & 1);
  const double cb = use_size_based_cb ? fitcbval (size) : 2.0;
  assert (cb);
  const double base = 1/cb;     // scores are 'base^0,base^1,base^2,...

  double next = 1;
  for (epsilon = next; next; next = epsilon*base)
    table.push_back (epsilon = next);

  PHASE ("walk", internal->stats.walk.count,
    "CB %.2f with inverse %.2f as base and table size %zd",
    cb, base, table.size ());
}

// The scores are tabulated for faster computation (to avoid 'pow').

inline double Walker::score (unsigned i) {
  const double res = (i < table.size () ? table[i] : epsilon);
  LOG ("break %u mapped to score %g", i, res);
  return res;
}

// can't store this online because we don't track satisfied constraints
int Internal::CARnSat (Clause *c) {
  int res = 0;
  int * lits = c->literals;
  const int size = c->size;
  for (int i = 0; i < size; i++) {
    const int lit = lits[i];
    assert (active (lit));  // Due to garbage collection.
    if (val (lit) > 0) res++;
  }
  return res;
}

/*------------------------------------------------------------------------*/

Clause * Internal::walk_pick_clause (Walker & walker) {
  require_mode (WALK);
  assert (!walker.broken.empty ());
  int64_t size = walker.broken.size ();
  if (size > INT_MAX) size = INT_MAX;
  int pos = walker.random.pick_int (0, size-1);
  Clause * res = walker.broken[pos];
  LOG (res, "picking clause from random position %d", pos);
  return res;
}

Clause * Internal::walk_pick_cardinality_constraint (Walker & walker) {
  require_mode (WALK);
  assert (!walker.broken_card.empty ());
  int64_t size = walker.broken_card.size ();
  if (size > INT_MAX) size = INT_MAX;
  int pos = walker.random.pick_int (0, size-1);

  pos = 0;

  Clause * res = walker.broken_card[pos];
  LOG (res, "picking cardinality constraint random position %d", pos);
  return res;
}

// Decide between picking an unsatisfied clause or cardinality constraint
Clause * Internal::walk_pick_constraint (Walker & walker) {
  Clause * res = NULL;

  // check if one stack is empty
  if (! walker.broken.size()) {
    res = walk_pick_cardinality_constraint (walker);
    return res;
  } else if (! walker.broken_card.size ()) {
    res = walk_pick_clause (walker);
    return res;
  }

  assert (walker.constraint_selection >= 0 && walker.constraint_selection < 4);
  if (walker.constraint_selection == 0) { // weighted random selection
    int64_t size_cls = walker.broken.size ();
    int64_t size_card = walker.broken_card.size ();
    int constraint_choice = walker.random.pick_int (0, size_cls+size_card-1);
    if (constraint_choice < size_cls)
      res = walk_pick_clause (walker);
    else
      res = walk_pick_cardinality_constraint (walker);
  } else if (walker.constraint_selection == 1) { // cardinality first
    if (walker.broken_card.size ())
      res = walk_pick_cardinality_constraint (walker);
    else 
      res = walk_pick_clause (walker);
  } else if (walker.constraint_selection == 2) { // clause first
    if (walker.broken.size ())
      res = walk_pick_clause (walker);
    else 
      res = walk_pick_cardinality_constraint (walker);
  } else if (walker.constraint_selection == 3) { // weighted random selection
    int constraint_choice = walker.random.pick_int (0, 1);
    if (constraint_choice < 1 )
      res = walk_pick_clause (walker);
    else
      res = walk_pick_cardinality_constraint (walker);
  }
  return res;
}

/*------------------------------------------------------------------------*/

// Compute the number of clauses which would be become unsatisfied if 'lit'
// is flipped and set to false.  This is called the 'break-count' of 'lit'.

unsigned Internal::walk_break_value (int lit, Walker &walker) {

  require_mode (WALK);
  assert (val (lit) > 0);

  unsigned res = 0;             // The computed break-count of 'lit'.

  for (auto & w : watches (lit)) {
    // split on cardinality constraint and clause
    const signed char b = (!w.cardinality_clause()) ? val (w.get_blit()) : 0;
    if (b > 0) {
      assert (w.get_blit () != lit);
      continue;
    }
    if (w.binary ()) { res++; continue; }
    
    if (!w.cardinality_clause()) { // normal clause
      assert (w.get_blit () != lit);
      
      Clause * c = w.clause;
      assert (lit == c->literals[0]);

      // Now try to find a second satisfied literal starting at 'literals[1]'
      // shifting all the traversed literals to right by one position in order
      // to move such a second satisfying literal to 'literals[1]'.  This move
      // to front strategy improves the chances to find the second satisfying
      // literal earlier in subsequent break-count computations.
      //
      auto begin = c->begin () + 1;
      const auto end = c->end ();
      auto i = begin;
      int prev = 0;
      while (i != end) {
        const int other = *i;
        *i++ = prev;
        prev = other;
        if (val (other) < 0) continue;

        // Found 'other' as second satisfying literal.

        w.set_blit (other);                   // Update 'blit'
        *begin = other;                   // and move to front.

        break;
      }

      if (i != end) continue;     // Double satisfied!

      // Otherwise restore literals (undo shift to the right).
      //
      while (i != begin) {
        const int other = *--i;
        *i = prev;
        prev = other;
      }

      res++;      // Literal 'lit' single satisfies clause 'c'.
    } else { // cardinality constraint

      Clause * c = w.clause;

      int nSat = CARnSat (c);
      int bound = c->CARbound ();

      if (walker.card_wt_rule == 0) {  // simplest, sigle break
        res++;
      } else if (walker.card_wt_rule == 1) { // linear break count
        res += (bound - nSat) + 1; // +1 for lit we are flipping
      } else if (walker.card_wt_rule == 2) { // multiplicative break
        res += ((bound - nSat) + 1) * c->size;
      } else if (walker.card_wt_rule == 3) { // quadratic break
        res += pow (((bound - nSat) + 1), 2);
      }
    }
  }

  return res;
}

/*------------------------------------------------------------------------*/

// Given an unsatisfied clause 'c', in which we want to flip a literal, we
// first determine the exponential score based on the break-count of its
// literals and then sample the literals based on these scores.  The CB
// value is smaller than one and thus the score is exponentially decreasing
// with the break-count increasing.  The sampling works as in 'ProbSAT' and
// 'YalSAT' by summing up the scores and then picking a random limit in the
// range of zero to the sum, then summing up the scores again and picking
// the first literal which reaches the limit.  Note, that during incremental
// SAT solving we can not flip assumed variables.  Those are assigned at
// decision level one, while the other variables are assigned at two.

int Internal::walk_pick_lit (Walker & walker, Clause * c) {
  LOG ("picking literal by break-count");
  assert (walker.scores.empty ());
  double sum = 0;
  int64_t propagations = 0;
  for (const auto lit : *c) {
    assert (active (lit));
    if (var (lit).level == 1) {
      LOG ("skipping assumption %d for scoring", -lit);
      continue;
    }
    if (val (lit) > 0) continue; // skipping true lit (card constraint)
    assert (active (lit));
    propagations++;
    unsigned tmp = walk_break_value (-lit, walker);
    double score = walker.score (tmp);
    assert (score > 0);
    LOG ("literal %d break-count %u score %g", lit, tmp, score);
    walker.scores.push_back (score);
    sum += score;
  }
  LOG ("scored %zd literals", walker.scores.size ());
  assert (!walker.scores.empty ());
  walker.propagations += propagations;
  stats.propagations.walk += propagations;
  assert (walker.scores.size () <= (size_t) c->size);
  const double lim = sum * walker.random.generate_double ();
  LOG ("score sum %g limit %g", sum, lim);
  const auto end = c->end ();
  auto i = c->begin ();
  auto j = walker.scores.begin ();
  int res;
  while (1) {
    assert (i != end);
    res = *i++;
    if (var (res).level <= 1) continue;
    if (val (res) > 0) continue;
    break;
    // LOG ("skipping assumption %d without score", -res);
  }
  sum = *j++;
  while (sum <= lim && i != end) {
    res = *i++;
    if (var (res).level == 1) {
      LOG ("skipping assumption %d without score", -res);
      continue;
    }
    if (val (res) > 0) continue; // skipping true lit (card constraint) 
    sum += *j++;
  }
  walker.scores.clear ();
  LOG ("picking literal %d by break-count", res);
  assert (val (res) < 0);
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::walk_flip_lit (Walker & walker, int lit) {

  require_mode (WALK);
  LOG ("flipping assign %d", lit);
  VERBOSE (3, "flipping assign %d", lit);
  assert (val (lit) < 0);

  // First flip the literal value.
  //
  const int tmp = sign (lit);
  const int idx = abs (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  assert (val (lit) > 0);

  // Then remove 'c' and all other now satisfied (made) clauses.
  {
    // Simply go over all unsatisfied (broken) clauses.

    LOG ("trying to make %zd broken clauses", walker.broken.size ());

    // We need to measure (and bound) the memory accesses during traversing
    // broken clauses in terms of 'propagations'. This is tricky since we
    // are not actually propagating literals.  Instead we use the clause
    // variable 'ratio' as an approximation to the number of clauses used
    // during propagating a literal.  Note that we use a one-watch scheme.
    // Accordingly the number of broken clauses traversed divided by that
    // ratio is an approximation of the number of propagation this would
    // correspond to (in terms of memory access).  To eagerly update these
    // statistics we simply increment the propagation counter after every
    // 'ratio' traversed clause.  These propagations are particularly
    // expensive if the number of broken clauses is large which usually
    // happens initially.
    //
    const double ratio = clause_variable_ratio ();
    const auto eou = walker.broken.end ();
    auto j = walker.broken.begin (), i = j;
    int64_t made = 0, count = 0;

    while (i != eou) {

      Clause * d = *j++ = *i++;

      int * literals = d->literals, prev = 0;

      // Find 'lit' in 'd'.
      //
      const int size = d->size;
      for (int i = 0; i < size; i++) {
        const int other = literals[i];
        assert (active (other));
        literals[i] = prev;
        prev = other;
        if (other == lit) break;
        assert (val (other) < 0);
      }

      // If 'lit' is in 'd' then move it to the front to watch it.
      //
      if (prev == lit) {
        literals[0] = lit;
        LOG (d, "made");
        watch_literal (literals[0], literals[1], d);
        made++;
        j--;

      } else {  // Otherwise the clause is not satisfied, undo shift.

        for (int i = size-1; i >= 0; i--) {
          int other = literals[i];
          literals[i] = prev;
          prev = other;
        }
      }

      if (count--) continue;

      // Update these counters eagerly.  Otherwise if we delay the update
      // until all clauses are traversed, interrupting the solver has a high
      // chance of giving bogus statistics on the number of 'propagations'
      // in 'walk', if it is interrupted in this loop.

      count = ratio;                    // Starting counting down again.
      walker.propagations++;
      stats.propagations.walk++;
    }
    LOG ("made %" PRId64 " clauses by flipping %d", made, lit);
    walker.broken.resize (j - walker.broken.begin ());
  }

  {
    // Simply go over all unsatisfied (broken) cardinality constraints.

    LOG ("trying to make %zd broken clauses", walker.broken_card.size ());

    const double ratio = clause_variable_ratio ();
    const auto eou = walker.broken_card.end ();
    auto j = walker.broken_card.begin (), i = j;
    int64_t made = 0, count = 0;

    while (i != eou) {

      Clause * d = *j++ = *i++;

      int * literals = d->literals, prev = -1;
      int bound = d->CARbound ();
      int nSat = CARnSat (d);

      // Find 'lit' in 'd'.
      //
      const int size = d->size;
      int lit_pos = 0, lit_it;
      int found_lit = false;
      for (lit_it = 0; lit_it < size; lit_it++) {
        const int other = literals[lit_it];
        assert (active (other));
        if (prev == -1 && val (other) < 0) prev = lit_it;
        // literals[i] = prev;
        // prev = other;
        if (other == lit) {found_lit = true; lit_pos = lit_it;}
        if (prev > -1 && found_lit) break;
      }

      if (literals[lit_pos] == lit) { // watch satisfied literal
        assert (lit);
        assert (val (lit) > 0);
        if (lit_pos >= bound) { // swap to front of constraint
          assert (prev > -1);
          assert (literals[prev]);
          assert (val (literals[prev]) < 0);
          assert (prev < bound);
          swap (literals[prev], literals[lit_pos]);
          CARwatch_literal (lit,prev, d);
        } else
          CARwatch_literal (lit,lit_pos, d);
      }

      assert (nSat <= bound);

      if (nSat == bound) { // made
        LOG (d, "made");
        made++;
        j--;
      } else {
        ; // do nothing here
      }

      if (count--) continue;

      // Update these counters eagerly.  Otherwise if we delay the update
      // until all clauses are traversed, interrupting the solver has a high
      // chance of giving bogus statistics on the number of 'propagations'
      // in 'walk', if it is interrupted in this loop.

      count = ratio;                    // Starting counting down again.
      walker.propagations++;
      stats.propagations.walk++;
    }
    LOG ("made %" PRId64 " cardinality constraints by flipping %d", made, lit);
    walker.broken_card.resize (j - walker.broken_card.begin ());
  }

  // Finally add all new unsatisfied (broken) clauses.
  {
    walker.propagations++;      // This really corresponds now to one
    stats.propagations.walk++;  // propagation (in a one-watch scheme).

    int64_t broken = 0;
    Watches & ws = watches (-lit);

    LOG ("trying to brake %zd watched clauses", ws.size ());

    for (const auto & w : ws) {
      if (w.cardinality_clause ()) continue;
      Clause * d = w.clause;
      LOG (d, "unwatch %d in", -lit);
      int * literals = d->literals, replacement = 0, prev = -lit;
      assert (literals[0] == -lit);
      const int size = d->size;
      for (int i = 1; i < size; i++) {
        const int other = literals[i];
        assert (active (other));
        literals[i] = prev;             // shift all to right
        prev = other;
        const signed char tmp = val (other);
        if (tmp < 0) continue;
        replacement = other;            // satisfying literal
        break;
      }
      if (replacement) {
        literals[1] = -lit;
        literals[0] = replacement;
        assert (-lit != replacement);
        watch_literal (replacement, -lit, d);
      } else {
        for (int i = size-1; i > 0; i--) {      // undo shift
          const int other = literals[i];
          literals[i] = prev;
          prev = other;
        }
        assert (literals[0] == -lit);
        LOG (d, "broken");
        walker.broken.push_back (d);
        broken++;
      }
    }
    LOG ("broken %" PRId64 " clauses by flipping %d", broken, lit);
    // ws.clear ();
  }

  // Finally add all new unsatisfied (broken) cardinality constraints.
  {
    walker.propagations++;      // This really corresponds now to one
    stats.propagations.walk++;  // propagation (in a one-watch scheme).

    int64_t broken = 0;
    Watches & ws = watches (-lit);

    LOG ("trying to brake %zd watched cardinality constraints", ws.size ());

    for (const auto & w : ws) {
      if (!w.cardinality_clause ()) continue;
      Clause * d = w.clause;
      LOG (d, "unwatch %d in", -lit);
      int nSat = CARnSat (d);
      if (nSat < d->CARbound () - 1) {
        // overly borken constraint
        ;
      }
      else if (nSat == d->CARbound () - 1) { // broken cardinality constraint
        LOG (d, "broken");
        walker.broken_card.push_back (d);
        broken++;
        // possibly swap with last satisfied
        // int lit_pos = w.get_blit ();
        // if (lit_pos != nSat && nSat > 0) {
        //   swap (d->literals[lit_pos], d->literals[nSat]);
        //   remove_watch (watches (d->literals[lit_pos]), d);
        //   CARwatch_literal (d->literals[lit_pos], lit_pos, d);
        // }
      } else { // find replacement watch pointer... (this is why we need to be sorted...)
        int * literals = d->literals, replacement = 0;
        const int size = d->size;
        int lit_pos = w.get_blit (); // position of literal for card constraints
        lit_pos = 0;
        for (int i = 0; i < size; i++) {
          const int other = literals[i];
          if (other == -lit) {lit_pos = i; break;}
        }
        assert (lit_pos < d->CARbound ());
        // if (literals[lit_pos] != -lit) {
        //   for (int k = 0; k < d->size; k++) printf ("%d ",literals[k]);
        //   printf (" bound %d, nsat %d, lit_pos %d, lit %d\n", d->CARbound (), nSat, lit_pos, lit);
        // }
        assert (lit_pos < d->size);
        assert (lit_pos >= 0);
        assert (literals[lit_pos] == -lit);
        int replacement_pos = 0;
        for (replacement_pos = d->CARbound (); replacement_pos < size; replacement_pos++) {
          const int other = literals[replacement_pos];
          assert (active (other));
          const signed char tmp = val (other);
          if (tmp < 0) continue;
          replacement = other;            // satisfying literal
          break;
        }
        swap (literals[replacement_pos], literals[lit_pos]);
        assert (replacement_pos != lit_pos);
        assert (lit_pos >= 0);
        assert (lit_pos < d->size);
        assert (replacement);
        assert (val (replacement) > 0);
        assert (lit_pos < d->CARbound ());
        CARwatch_literal (replacement,lit_pos, d);
      }
    }
    LOG ("broken %" PRId64 " cardinality constraints by flipping %d", broken, lit);
    ws.clear ();
  }
}

/*------------------------------------------------------------------------*/

// Check whether to save the current phases as new global minimum.

inline void Internal::walk_save_minimum (Walker & walker) {
  int64_t broken = walker.broken.size ();
  int64_t broken_card = walker.broken_card.size ();
  if (broken + broken_card >= stats.walk.minimum) return;
  VERBOSE (2, "new global minimum clauses  %" PRId64 " cardinality constraints %" PRId64, broken, broken_card);
  stats.walk.minimum = broken + broken_card;
  for (auto i : vars) {
    const signed char tmp = vals[i];
    if (tmp)
      phases.min[i] = phases.saved[i] = tmp;
  }
}

/*------------------------------------------------------------------------*/

int Internal::walk_round (int64_t limit, bool prev) {

  backtrack ();
  if (propagated < trail.size () && !propagate ()) {
    LOG ("empty clause after root level propagation");
    learn_empty_clause ();
    return 20;
  }

  stats.walk.count++;

  clear_watches ();

  CARwatch_in_garbage = 0;
  // Remove all fixed variables first (assigned at decision level zero).
  //
  if (last.collect.fixed < stats.all.fixed)
    garbage_collection ();

  CARwatch_in_garbage = 1;
  // clear_watches (); // some things are watched in garbage collection
  

#ifndef QUIET
  // We want to see more messages during initial local search.
  //
  if (localsearching) {
    assert (!force_phase_messages);
    force_phase_messages = true;
  }
#endif

  PHASE ("walk", stats.walk.count,
    "random walk limit of %" PRId64 " propagations", limit);

  // First compute the average clause size for picking the CB constant.
  //
  double size = 0;
  int64_t n = 0;
  for (const auto c : clauses) {
    if (c->garbage) continue;
    if (c->redundant) {
      if (!opts.walkredundant) continue;
      if (!likely_to_be_kept_clause (c)) continue;
    }
    size += c->size;
    n++;
  }
  double average_size = relative (size, n);

  PHASE ("walk", stats.walk.count,
    "%" PRId64 " clauses average size %.2f over %d variables",
    n, average_size, active ());

  // Instantiate data structures for this local search round.
  //
  Walker walker (internal, average_size, limit);

  bool failed = false;  // Inconsistent assumptions?

  level = 1;    // Assumed variables assigned at level 1.

  if (assumptions.empty ()) {
    LOG ("no assumptions so assigning all variables to decision phase");
  } else {
    LOG ("assigning assumptions to their forced phase first");
    for (const auto lit : assumptions) {
      signed char tmp = val (lit);
      if (tmp > 0) continue;
      if (tmp < 0) {
        LOG ("inconsistent assumption %d", lit);
        failed = true;
        break;
      }
      if (!active (lit)) continue;
      tmp = sign (lit);
      const int idx = abs (lit);
      LOG ("initial assign %d to assumption phase", tmp < 0 ? -idx : idx);
      vals[idx] = tmp;
      vals[-idx] = -tmp;
      assert (level == 1);
      var (idx).level = 1;
    }
    if (!failed)
      LOG ("now assigning remaining variables to their decision phase");
  }

  level = 2;    // All other non assumed variables assigned at level 2.

  if (!failed) {

    for (auto idx : vars) {
      if (!active (idx)) {
        LOG ("skipping inactive variable %d", idx);
        continue;
      }
      if (vals[idx]) {
        assert (var (idx).level == 1);
        LOG ("skipping assumed variable %d", idx);
        continue;
      }
      int tmp = 0;
      if (prev) tmp = phases.prev[idx];
      if (!tmp) tmp = sign (decide_phase (idx, true));
      assert (tmp == 1 || tmp == -1);
      vals[idx] = tmp;
      vals[-idx] = -tmp;
      assert (level == 2);
      var (idx).level = 2;
      LOG ("initial assign %d to decision phase", tmp < 0 ? -idx : idx);
    }

    LOG ("watching satisfied and registering broken clauses");
#ifdef LOGGING
    int64_t watched = 0;
#endif
    for (const auto c : clauses) {

      if (c->garbage) continue;
      if (c->redundant) {
        if (!opts.walkredundant) continue;
        if (!likely_to_be_kept_clause (c)) continue;
      }

      bool satisfiable = false;         // contains not only assumptions
      int satisfied = 0;                // clause satisfied?

      int * lits = c->literals;
      const int size = c->size;

      // Move to front satisfied literals and determine whether there
      // is at least one (non-assumed) literal that can be flipped.
      //
      for (int i = 0; satisfied < 2 && i < size; i++) {
        const int lit = lits[i];
        assert (active (lit));  // Due to garbage collection.
        if (val (lit) > 0) {
          swap (lits[satisfied], lits[i]);
          if (!satisfied++) LOG ("first satisfying literal %d", lit);
        } else if (!satisfiable && var (lit).level > 1) {
          LOG ("non-assumption potentially satisfying literal %d", lit);
          satisfiable = true;
        }
      }

      if (!satisfied && !satisfiable) {
        LOG (c, "due to assumptions unsatisfiable");
        LOG ("stopping local search since assumptions falsify a clause");
        failed = true;
        break;
      }

      if (satisfied) {
        watch_literal (lits[0], lits[1], c);
#ifdef LOGGING
        watched++;
#endif
      } else {
        assert (satisfiable);   // at least one non-assumed variable ...
        LOG (c, "broken");
        walker.broken.push_back (c);
      }
    }
#ifdef LOGGING
    if (!failed) {
      int64_t broken = walker.broken.size ();
      int64_t total = watched + broken;
      LOG ("watching %" PRId64 " clauses %.0f%% "
           "out of %" PRId64 " (watched and broken)",
        watched, percent (watched, total), total);
    }
#endif

LOG ("watching satisfied and registering broken cardinality constraints");
#ifdef LOGGING
    watched = 0;
#endif
    for (const auto c : CARclauses) {

      if (c->garbage) continue;
      if (c->redundant) {
        if (!opts.walkredundant) continue;
        if (!likely_to_be_kept_clause (c)) continue;
      }

      if (c->guard_literal && val (c->guard_literal) > 0) continue;

      bool satisfiable = false;         // contains not only assumptions
      int satisfied = 0;                // clause satisfied?
      int unassigned = 0;               // clause satisfied?
      int bound = c->CARbound ();       // bound

      int * lits = c->literals;
      const int size = c->size;

      // Move to front satisfied literals and determine whether there
      // is at least one (non-assumed) literal that can be flipped.
      //
      for (int i = 0; i < size; i++) {
        const int lit = lits[i];
        assert (active (lit));  // Due to garbage collection.
        if (val (lit) > 0) {
          swap (lits[satisfied], lits[i]);
          satisfied++;
          LOG ("Satisfying literal %d", lit);
        } else if (var (lit).level > 1) {
          LOG ("non-assumption potentially satisfying literal %d", lit);
          unassigned++;
        }
      }

      satisfiable = (unassigned + satisfied >= bound);

      assert (satisfiable);

      if (!satisfiable) {
        LOG (c, "due to assumptions unsatisfiable");
        LOG ("stopping local search since assumptions falsify a clause");
        failed = true;
        break;
      }

      // watch all satisfied literals
      for (int i = 0; i < satisfied && i < bound; i++) {
        assert (val (lits[i]) > 0);
        CARwatch_literal (lits[i],i, c);
      }

      if (satisfied >= bound) {
        ;
#ifdef LOGGING
        watched+=bound;
#endif
      } else { // falsified
        assert (satisfiable);   // at least one non-assumed variable ...
        LOG (c, "broken");
        walker.broken_card.push_back (c);
      }
    }
#ifdef LOGGING
    if (!failed) {
      int64_t broken = walker.broken_card.size ();
      int64_t total = watched + broken;
      LOG ("watching %" PRId64 " card constraints %.0f%% "
           "out of %" PRId64 " (watched and broken)",
        watched, percent (watched, total), total);
    }
#endif

  }

  int64_t old_global_minimum = stats.walk.minimum;

  int res;      // Tells caller to continue with local search.

  if (!failed) {

    int64_t broken = walker.broken.size ();
    int64_t broken_card = walker.broken_card.size ();

    PHASE ("walk", stats.walk.count,
     "starting with %" PRId64 " unsatisfied clauses %" PRId64 " unsatisfied constraints "
     "(%.0f%% out of %" PRId64 ")",
     broken, broken_card, percent (broken, stats.current.irredundant),
     stats.current.irredundant);

    walk_save_minimum (walker);

    int64_t flips = 0, minimum = broken + broken_card;
    while (!terminated_asynchronously () &&
           (!walker.broken.empty () || !walker.broken_card.empty()) &&
           walker.propagations < walker.limit) {
      flips++;
      stats.walk.flips++;
      stats.walk.broken += broken;
      Clause * c = walk_pick_constraint (walker);
      const int lit = walk_pick_lit (walker, c);
      walk_flip_lit (walker, lit);
      broken = walker.broken.size ();
      broken_card = walker.broken_card.size ();
      LOG ("now have %" PRId64 " broken clauses %" PRId64 " broken cardinality constraints", broken, broken_card);
      VERBOSE (3, "now have %" PRId64 " broken clauses %" PRId64 " broken cardinality constraints", broken, broken_card);
      if (broken+broken_card >= minimum) continue;
      minimum = broken + broken_card;
      VERBOSE (2,
        "new phase minimum %" PRId64 " after %" PRId64 " flips",
        minimum, flips);
      walk_save_minimum (walker);
    }

    if (minimum < old_global_minimum)
      PHASE ("walk", stats.walk.count,
        "%snew global minimum %" PRId64 "%s in %" PRId64 " flips and "
        "%" PRId64 " propagations",
        tout.bright_yellow_code (), minimum, tout.normal_code (),
        flips, walker.propagations);
    else
      PHASE ("walk", stats.walk.count,
        "best phase minimum %" PRId64 " in %" PRId64 " flips and "
        "%" PRId64 " propagations",
        minimum, flips, walker.propagations);

    PHASE ("walk", stats.walk.count,
      "%.2f million propagations per second",
      relative (1e-6*walker.propagations,
      time () - profiles.walk.started));

    PHASE ("walk", stats.walk.count,
      "%.2f thousand flips per second",
      relative (1e-3*flips, time () - profiles.walk.started));

    if (minimum > 0) {
      LOG ("minimum %" PRId64 " non-zero thus potentially continue", minimum);
      res = 0;
    } else {
      LOG ("minimum is zero thus stop local search");
      res = 10;
    }

  } else {

    res = 20;

    PHASE ("walk", stats.walk.count,
      "aborted due to inconsistent assumptions");
  }

  copy_phases (phases.prev);

  for (auto idx : vars)
    if (active (idx))
      vals[idx] = vals[-idx] = 0;

  assert (level == 2);
  level = 0;

  clear_watches ();
  connect_watches ();

#ifndef QUIET
  if (localsearching) {
    assert (force_phase_messages);
    force_phase_messages = false;
  }
#endif

  return res;
}

void Internal::walk () {
  START_INNER_WALK ();
  // printf("start walk\n");
  int64_t limit = stats.propagations.search;
  limit *= 1e-3 * opts.walkreleff;
  if (limit < opts.walkmineff) limit = opts.walkmineff;
  if (limit > opts.walkmaxeff) limit = opts.walkmaxeff;
  (void) walk_round (limit, false);
  // printf("stop walk\n");
  STOP_INNER_WALK ();
}

}
