#include "internal.hpp"

namespace CaDiCaL {

void Internal::init_watches () {
  assert (wtab.empty ());
  if (wtab.size () < 2*vsize)
    wtab.resize (2*vsize, Watches ());
  LOG ("initialized watcher tables");
}

void Internal::clear_watches () {
  for (auto lit : lits)
    watches (lit).clear ();
}

void Internal::reset_watches () {
  assert (!wtab.empty ());
  erase_vector (wtab);
  LOG ("reset watcher tables");
}

// This can be quite costly since lots of memory is accessed in a rather
// random fashion, and thus we optionally profile it.

void Internal::connect_watches (bool irredundant_only) {
  START (connect);
  assert (watching ());

  LOG ("watching all %sclauses", irredundant_only ? "irredundant " : "");

  // First connect binary clauses.
  //
  for (const auto & c : clauses) {
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size > 2) continue;
    watch_clause (c);
  }
  
  if (opts.ccdclWatch) {
    if (ccdclHybridMode == 0 || ccdclHybridMode == 1) {
    // Then connect cardinality clauses.
    for (const auto & c : CARclauses) {
      if (c->garbage) continue;
      if (irredundant_only && c->redundant) continue;
      CARwatch_clause (c, c->unwatched-1);
    }
    }
    if (ccdclHybridMode == 0 || ccdclHybridMode == 2) {
    // Then connect cardinality clauses.
    for (const auto & c : CARencodingClauses) {
      if (c->garbage) continue;
      if (irredundant_only && c->redundant) continue;
      watch_clause (c);
    }
    }
  } 

  // Then connect non-binary clauses.
  //
  for (const auto & c : clauses) {
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size == 2) continue;
    watch_clause (c);
    if (!level) {
      const int lit0 = c->literals[0];
      const int lit1 = c->literals[1];
      const signed char tmp0 = val (lit0);
      const signed char tmp1 = val (lit1);
      if (tmp0 > 0) continue;
      if (tmp1 > 0) continue;
      if (tmp0 < 0) {
        const size_t pos0 = var (lit0).trail;
        if (pos0 < propagated) {
          propagated = pos0;
          LOG ("literal %d resets propagated to %zd", lit0, pos0);
        }
      }
      if (tmp1 < 0) {
        const size_t pos1 = var (lit1).trail;
        if (pos1 < propagated) {
          propagated = pos1;
          LOG ("literal %d resets propagated to %zd", lit1, pos1);
        }
      }
    }
  }

  if (!opts.ccdclWatch) {
    // Then connect cardinality clauses.
        // if (ccdclHybridMode == 0 || ccdclHybridMode == 1 || ccdclHybridMode == 2) {
        if (ccdclHybridMode == 0 || ccdclHybridMode == 1) {
    // Then connect cardinality clauses.
    for (const auto & c : CARclauses) {
      if (c->garbage) continue;
      if (irredundant_only && c->redundant) continue;
      CARwatch_clause (c, c->unwatched-1);
    }
    }
    if (ccdclHybridMode == 0 || ccdclHybridMode == 2) {
    // Then connect cardinality clauses.
    for (const auto & c : CARencodingClauses) {
      if (c->garbage) continue;
      if (irredundant_only && c->redundant) continue;
      watch_clause (c);
    }
    }
  }


  // watch guarded literals
  if (are_guarded_constraints) {
    for (const auto & c : CARclauses) {
        if (c->garbage) continue;
        if (irredundant_only && c->redundant) continue;
        if (c->guard_literal)
          CARwatch_guard (c->guard_literal, c);
    }
  }

  STOP (connect);
}

void Internal::connect_vivify_watches (bool irredundant_only) {
  START (connect);
  assert (watching ());

  LOG ("watching all %sclauses", irredundant_only ? "irredundant " : "");

  // First connect binary clauses.
  //
  for (const auto & c : clauses) {
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size > 2) continue;
    watch_clause (c);
  }

  // Then connect non-binary clauses.
  //
  for (const auto & c : clauses) {
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size == 2) continue;
    watch_clause (c);
    if (!level) {
      const int lit0 = c->literals[0];
      const int lit1 = c->literals[1];
      const signed char tmp0 = val (lit0);
      const signed char tmp1 = val (lit1);
      if (tmp0 > 0) continue;
      if (tmp1 > 0) continue;
      if (tmp0 < 0) {
        const size_t pos0 = var (lit0).trail;
        if (pos0 < propagated) {
          propagated = pos0;
          LOG ("literal %d resets propagated to %zd", lit0, pos0);
        }
      }
      if (tmp1 < 0) {
        const size_t pos1 = var (lit1).trail;
        if (pos1 < propagated) {
          propagated = pos1;
          LOG ("literal %d resets propagated to %zd", lit1, pos1);
        }
      }
    }
  }

  if (!ccdclHybridMode) {
    // Then connect cardinality clauses.
    for (const auto & c : CARclauses) {
      if (c->garbage) continue;
      if (irredundant_only) continue;
      CARwatch_clause (c, c->unwatched-1);
    }
  }

  STOP (connect);
}

void Internal::sort_watches () {
  assert (watching ());
  LOG ("sorting watches");
  Watches saved;
  for (auto lit : lits) {
    Watches & ws = watches (lit);

    const const_watch_iterator end = ws.end ();
    watch_iterator j = ws.begin ();
    const_watch_iterator i;

    assert (saved.empty ());

    for (i = j; i != end; i++) {
      const Watch w = *i;
      if (w.binary ()) *j++ = w;
      else saved.push_back (w);
    }

    std::copy (saved.cbegin (), saved.cend (), j);

    saved.clear ();
  }
}

}
