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
  $Header: /cvsroot/buddy/buddy/src/cache.h,v 1.1.1.1 2004/06/25 13:22:34 haimcohen Exp $
  FILE:  cache.h
  DESCR: Cache class for caching apply/exist etc. results
  AUTH:  Jorn Lind
  DATE:  (C) june 1997
*************************************************************************/

/*************************************************************************
  Modified 2022/02/10.  R.E. Bryant
  Create four cache operands (a, b, c, op) so that single cache would suffice for all operations
*************************************************************************/

#ifndef _CACHE_H
#define _CACHE_H

#ifndef ENABLE_TBDD
#define ENABLE_TBDD 0
#endif

typedef struct
{
   union
   {
      double dres;
#if ENABLE_TBDD
       // C compiler needs to support anonymous structs
       struct {
	   BDD res;
	   int jclause;
       };
#else
       int res;
#endif       
   } r;
   int a,b,c;
   int op;
} BddCacheData;


typedef struct
{
   BddCacheData *table;
   int tablesize;
} BddCache;

extern int  BddCache_init(BddCache *, int);
extern void BddCache_done(BddCache *);
extern int  BddCache_resize(BddCache *, int);
extern void BddCache_reset(BddCache *);

#if ENABLE_TBDD
extern void BddCache_clause_evict(BddCacheData *entry);
extern void BddCache_clear_clauses(BddCache *);
#endif

#define BddCache_lookup(cache, hash) (&(cache)->table[hash % (cache)->tablesize])


#endif /* _CACHE_H */


/* EOF */
