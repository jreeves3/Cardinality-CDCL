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


#ifndef _ILIST_H
#define _ILIST_H

#include <stdio.h>
#include <stdbool.h>
#include <limits.h>


/*============================================
   Integer lists
============================================*/

/* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

#ifdef CPLUSPLUS
extern "C" {
#endif

/*
  Data type ilist is used to represent clauses and clause id lists.
  These are simply lists of integers, where the value at position -1
  indicates the list length and the value at position -2 indicates the
  maximum list length.  The value at position -2 is positive for
  statically-allocated ilists and negative for ones that can be
  dynamically resized.
*/
typedef int *ilist;
  
/*
  Difference between ilist maximum length and number of allocated
  integers
 */
#define ILIST_OVHD 2

/*
  Pseudo-clause representing tautology
 */
#define TAUTOLOGY_CLAUSE ((ilist) INT_MAX)

/*
  Pseudo-cube representing falsehood
 */
#define FALSE_CUBE ((ilist) INT_MIN)

/* 
   Convert an array of ints to an ilist.  Don't call free_ilist on
   this one!  The size of the array should be max_length + ILIST_OVHD
   Will be statically sized
*/
extern ilist ilist_make(int *p, int max_length);

/* Allocate a new ilist. */
extern ilist ilist_new(int max_length);

/* Free allocated ilist.  Will only free ones allocated via ilist_new */
extern void ilist_free(ilist ils);

/* Return number of elements in ilist */
extern int ilist_length(ilist ils);

/*
  Change size of ilist.  Can be shorter or longer than current.
  When lengthening, new contents are undefined
*/
extern ilist ilist_resize(ilist ils, int nlength);

/*
  Add new value(s) to end of ilist.
  For dynamic ilists, the value of the pointer may change
*/
extern ilist ilist_push(ilist ils, int val);

/*
  Populate ilist with 1, 2, 3, or 4 elements.
  For dynamic ilists, the value of the pointer may change
 */
extern ilist ilist_fill1(ilist ils, int val1);
extern ilist ilist_fill2(ilist ils, int val1, int val2);
extern ilist ilist_fill3(ilist ils, int val1, int val2, int val3);
extern ilist ilist_fill4(ilist ils, int val1, int val2, int val3, int val4);

/*
  Test whether value is member of list
 */
extern bool ilist_is_member(ilist ils, int val);

/*
  Dynamically allocate ilist and copy from existing one.
 */
extern ilist ilist_copy(ilist ils);

/*
  Dynamically allocate ilist and fill from array
 */
extern ilist ilist_copy_list(int *ls, int length);

/*
  Dynamically allocate ilist and fill with numbers from a text file
  Return NULL if invalid number encountered
 */
extern ilist ilist_read_file(FILE *infile);

/*
  Reverse elements in ilist
 */
extern void ilist_reverse(int *ls);

/*
  Put elements of ilist into ascending order
 */
extern void ilist_sort(int *ls);

/*
  Print elements of an ilist separated by sep.  Return value < 0 if error
 */
extern int ilist_print(ilist ils, FILE *out, const char *sep);

/*
  Format string of elements of an ilist separated by sep.  Return number of characters written
 */
extern int ilist_format(ilist ils, char *out, const char *sep, int maxlen);
    

#ifdef CPLUSPLUS
}
#endif

#if 0 /* DISABLE */
#ifdef CPLUSPLUS
/* This API has not been tested, and it isn't compatible with the C++ API for TBDD */
class Ilist {

public:
    
    inline Ilist(int *buf, int max_length) { list = ilist_make(buf, max_length); }
    inline Ilist(int max_length) { list = ilist_new(max_length); } 
    inline ~Ilist() { ilist_free(list); }
    inline void push(int val) { list = ilist_push(list, val); }
    inline void fill1(int val1) { list = ilist_fill1(list, val1); }
    inline void fill2(int val1, int val2) { list = ilist_fill2(list, val1, val2); }
    inline void fill3(int val1, int val2, int val3) { list = ilist_fill3(list, val1, val2, val3); }
    inline void fill4(int val1, int val2, int val3, int val4) { list = ilist_fill4(list, val1, val2, val3, val4); }
    inline void resize(int nlength) { list = ilist_resize(list, nlength); }
    inline int length()  { return ilist_length(list); }
    inline void print(FILE *out, const char *sep) { ilist_print(list, out, sep); }
    inline void format(char *out, const char *sep, int maxlen) { ilist_format(list, out, sep, maxlen); }
    inline int& operator[](int i) { return list[i]; }
private:
    ilist list;


};
#endif /* C++ */
#endif /* DISABLE */

#endif /* _ILIST_H */
/* EOF */

