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
#include "ilist.h"

#ifdef ENABLE_TBDD
int bdd_error(int);
#define ILIST_ALLOC (-23)
#endif

#define ERROUT stdout

/*============================================
   Integer lists
============================================*/

/* Macros */
#define ILIST_BASE(ils) ((ils)-ILIST_OVHD)
#define ILIST_LENGTH(ils) ((ils)[-1])
#define IABS(x) ((x)<0?(-x):(x))
#define ILIST_MAXLENGTHFIELD(ils) ((ils)[-2])
#define ILIST_MAXLENGTH(ils) (IABS(ILIST_MAXLENGTHFIELD(ils)))

static ilist ilist_error(char *fname) {
    fprintf(ERROUT, "ilist error in %s\n", fname);
#if ENABLE_TBDD
    bdd_error(ILIST_ALLOC);
#else
    exit(1);
#endif
    return NULL;
}

/* 
   Convert an array of ints to an ilist.  Don't call free_ilist on
   this one!  The size of the array should be max_length + ILIST_OVHD
   Will be statically sized
*/
ilist ilist_make(int *p, int max_length) {
    ilist result = p+ILIST_OVHD;
    ILIST_LENGTH(result) = 0;
    ILIST_MAXLENGTHFIELD(result) = max_length;
    return result;
}

/* Allocate a new ilist. */
ilist ilist_new(int max_length) {
    if (max_length == 0)
	max_length++;
    int *p = calloc(max_length + ILIST_OVHD, sizeof(int));
     ilist result = p+ILIST_OVHD;
    ILIST_LENGTH(result) = 0;
    ILIST_MAXLENGTHFIELD(result) = -max_length;
    return result;
}

/* Free allocated ilist.  Will only free ones allocated via ilist_new */
void ilist_free(ilist ils) {
    if (!ils)
	return;
    if (ILIST_MAXLENGTHFIELD(ils) < 0) {
	int *p = ILIST_BASE(ils);
	free(p);
    }
}

/* Return number of elements in ilist */
int ilist_length(ilist ils) {
    if (ils == TAUTOLOGY_CLAUSE)
	return 0;
    return ILIST_LENGTH(ils);
}

/*
  Change size of ilist.  Can be shorter or longer than current.
  When lengthening, new contents are undefined
*/
ilist ilist_resize(ilist ils, int nlength) {
    int list_max_length = ILIST_MAXLENGTHFIELD(ils);
    int true_max_length = IABS(list_max_length);
    if (nlength > true_max_length) {
	if (list_max_length < 0) {
	    int *p = ILIST_BASE(ils);
	    int old_tml = true_max_length;
	    /* Dynamically resize */
	    true_max_length *= 2;
	    if (nlength > true_max_length)
		true_max_length = nlength;
	    p = realloc(p, (true_max_length + ILIST_OVHD) * sizeof(int));
	    if (p == NULL) {
		/* Need to throw error here */
		fprintf(ERROUT, "Failed to grow ilist allocation from %d to %d\n",
			old_tml, true_max_length);
		return ilist_error("resize (dynamic)");
	    }
	    ils = p+ILIST_OVHD;
	    ILIST_MAXLENGTHFIELD(ils) = -true_max_length;
	} else 
	    /* Need to throw an error here */
	    return ilist_error("resize (static)");
    }
    ILIST_LENGTH(ils) = nlength;
    return ils;
}

/*
  Add new value(s) to end of ilist.
  For dynamic ilists, the value of the pointer may change
*/
ilist ilist_push(ilist ils, int val) {
    int length = ILIST_LENGTH(ils);
    int nlength = length+1;
    ils = ilist_resize(ils, nlength);
    if (!ils) {
	/* Want to throw an exception here */
	return ilist_error("push");
    }
    ils[length] = val;
    ILIST_LENGTH(ils) = nlength;
    return ils;
}

/*
  Populate ilist with 1, 2, 3, or 4 elements.
  For dynamic ilists, the value of the pointer may change
 */
ilist ilist_fill1(ilist ils, int val1) {
    ils = ilist_resize(ils, 1);
    if (!ils) {
	/* Want to throw an exception here */
	return ilist_error("fill1");
    }
    ils[0] = val1;
    return ils;
}

ilist ilist_fill2(ilist ils, int val1, int val2) {
    ils = ilist_resize(ils, 2);
    if (!ils) {
	/* Want to throw an exception here */
	return ilist_error("fill2");
    }
    ils[0] = val1;
    ils[1] = val2;
    return ils;
}

ilist ilist_fill3(ilist ils, int val1, int val2, int val3) {
    ils = ilist_resize(ils, 3);
    if (!ils) {
	/* Want to throw an exception here */
	return ilist_error("fill3");
    }
    ils[0] = val1;
    ils[1] = val2;
    ils[2] = val3;
    return ils;
}

ilist ilist_fill4(ilist ils, int val1, int val2, int val3, int val4) {
    ils = ilist_resize(ils, 4);
    if (!ils) {
	/* Want to throw an exception here */
	return ilist_error("fill4");
    }
    ils[0] = val1;
    ils[1] = val2;
    ils[2] = val3;
    ils[3] = val4;
    return ils;
}

/*
  Dynamically allocate ilist and fill from array
 */
ilist ilist_copy_list(int *ls, int length) {
    ilist rils =  ilist_new(length);
    rils = ilist_resize(rils, length);
    memcpy(rils, ls, length*sizeof(int));
    return rils;
}

/*
  Dynamically allocate ilist and fill with numbers from a text file
  Return NULL if invalid number encountered
 */
ilist ilist_read_file(FILE *infile) {
    ilist rils = ilist_new(1);
    int val;
    int rcode;
    while ((rcode = fscanf(infile, "%d", &val)) == 1) {
	rils = ilist_push(rils, val);
    }
    if (rcode != EOF)
	return NULL;
    return rils;
}


/*
  Test whether value is member of list
 */
extern bool ilist_is_member(ilist ils, int val) {
    int i;
    for (i = 0; i < ilist_length(ils); i++)
	if (val == ils[i])
	    return true;
    return false;
}

/*
  Dynamically allocate ilist and copy from existing one.
 */
ilist ilist_copy(ilist ils) {
    ilist rils = ilist_copy_list(ils, ilist_length(ils));
    return rils;
}

/*
  Reverse elements in ilist
 */
void ilist_reverse(int *ils) {
    int left = 0;
    int right = ilist_length(ils)-1;
    while (left < right) {
	int v = ils[left];
	ils[left] = ils[right];
	ils[right] = v;
	left++;
	right--;
    }
}

/*
  Sort integers in ascending order
 */
int int_compare_ilist(const void *i1p, const void *i2p) {
    int i1 = *(int *) i1p;
    int i2 = *(int *) i2p;
    if (i1 < i2)
	return -1;
    if (i1 > i2)
	return 1;
    return 0;
}


/*
  Put elements of ilist into ascending order
 */
void ilist_sort(int *ils) {
    qsort((void *) ils, ilist_length(ils), sizeof(int), int_compare_ilist);
}


/*
  Print elements of an ilist separated by sep
 */
int ilist_print(ilist ils, FILE *out, const char *sep) {
    int i;
    int rval = 0;
    const char *space = "";
    if (ils == TAUTOLOGY_CLAUSE) {
	rval = fprintf(out, "TAUT");
	return rval;
    }
    if (ils == NULL) {
	rval = fprintf(out, "NULL");
	return rval;
    }
    for (i = 0; i < ilist_length(ils); i++) {
	int pval = fprintf(out, "%s%d", space, ils[i]);
	if (pval < 0)
	    return pval;
	rval += pval;
	space = sep;
    }
    return rval;
}

/*
  Print elements of an ilist separated by sep.  Return number of characters written
 */
int ilist_format(ilist ils, char *out, const char *sep, int maxlen) {
    int i;
    const char *space = "";
    if (ils == TAUTOLOGY_CLAUSE) {
	return snprintf(out, maxlen, "TAUT");
    }
    int len = 0;
    for (i = 0; i < ilist_length(ils); i++) {
	if (len >= maxlen)
	    break;
	int xlen = snprintf(out+len, maxlen-len, "%s%d", space, ils[i]);
	len += xlen;
	space = sep;
    }
    out[len] = '\0';
    return len;
}
