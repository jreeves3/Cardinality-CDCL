/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
  As noted below, this code is a modified version of code authored and
  copywrited by Jorn Lind-Nielsen.  Permisssion to use the original
  code is subject to the terms noted below.

  Regarding the modifications, and subject to any constraints on the
  use of the original code, permission is hereby granted, free of
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


/*========================================================================
               Copyright (C) 1996-2002 by Jorn Lind-Nielsen
                            All rights reserved

    Permission is hereby granted, without written agreement and without
    license or royalty fees, to use, reproduce, prepare derivative
    works, distribute, and display this software and its documentation
    for any purpose, provided that (1) the above copyright notice and
    the following two paragraphs appear in all copies of the source code
    and (2) redistributions, including without limitation binaries,
    reproduce these notices in the supporting documentation. Substantial
    modifications to this software may be copyrighted by their authors
    and need not follow the licensing terms described here, provided
    that the new terms are clearly indicated in all files where they apply.

    IN NO EVENT SHALL JORN LIND-NIELSEN, OR DISTRIBUTORS OF THIS
    SOFTWARE BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
    INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS
    SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE AUTHORS OR ANY OF THE
    ABOVE PARTIES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    JORN LIND-NIELSEN SPECIFICALLY DISCLAIM ANY WARRANTIES, INCLUDING,
    BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS
    ON AN "AS IS" BASIS, AND THE AUTHORS AND DISTRIBUTORS HAVE NO
    OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
    MODIFICATIONS.
========================================================================*/

/*************************************************************************
  $Header: /cvsroot/buddy/buddy/src/cache.c,v 1.1.1.1 2004/06/25 13:22:34 haimcohen Exp $
  FILE:  cache.c
  DESCR: Cache class for caching apply/exist etc. results in BDD package
  AUTH:  Jorn Lind
  DATE:  (C) june 1997
*************************************************************************/
#include <stdlib.h>
#include "kernel.h"
#include "cache.h"
#include "prime.h"

/*************************************************************************
*************************************************************************/

int BddCache_init(BddCache *cache, int size)
{
   int n;

   size = bdd_prime_gte(size);
   
   if ((cache->table=NEW(BddCacheData,size)) == NULL)
      return bdd_error(BDD_MEMORY);
   
   for (n=0 ; n<size ; n++)
      cache->table[n].a = -1;
   cache->tablesize = size;
   
   return 0;
}


void BddCache_done(BddCache *cache)
{
   free(cache->table);
   cache->table = NULL;
   cache->tablesize = 0;
}


int BddCache_resize(BddCache *cache, int newsize)
{
   int n;

   free(cache->table);

   newsize = bdd_prime_gte(newsize);
   
   if ((cache->table=NEW(BddCacheData,newsize)) == NULL)
      return bdd_error(BDD_MEMORY);
   
   for (n=0 ; n<newsize ; n++)
      cache->table[n].a = -1;
   cache->tablesize = newsize;
   
   return 0;
}


void BddCache_reset(BddCache *cache)
{
   register int n;
   for (n=0 ; n<cache->tablesize ; n++)
      cache->table[n].a = -1;
}

#if ENABLE_TBDD
void BddCache_clause_evict(BddCacheData *entry) {
    int id;
    if (entry->a != -1 &&
	(entry->op == bddop_andimptstj || entry->op == bddop_andj || entry->op == bddop_imptstj)) {
	id = entry->r.jclause;
	if (id == TAUTOLOGY)
	    return;
#if DO_TRACE
	if (NNAME(entry->r.res) == TRACE_NNAME) {
	    printf("TRACE: Evicting node N%d.  Deleting clause %d\n", TRACE_NNAME, entry->r.jclause);
	}
#endif	
	defer_delete_clause(id);
    }
}

void BddCache_clear_clauses(BddCache *cache)
{
   register int n;
   print_proof_comment(2, "Deleting justifying clauses for cached operations");
   for (n=0 ; n<cache->tablesize ; n++) {
       BddCacheData *entry = &cache->table[n];
       BddCache_clause_evict(entry);
   }
}
#endif


/* EOF */
