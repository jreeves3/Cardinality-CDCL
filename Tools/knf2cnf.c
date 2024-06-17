#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

//#define PAIRWISE
//#define CNFPLUS
//#define DERIVATION
//#define KONLY
//#define LINEAR

// just a clause
void atleastone (int *array, int size) {
  for (int i = 0; i < size; i++)
    printf ("%i ", array[i]);
  printf ("0\n");
}

// no auxiliary variables for at least two
void atleasttwo (int *array, int size) {
  for (int i = size-1; i >= 0; i--) {
    for (int j = 0; j < size; j++)
      if (j != i) printf ("%i ", array[j]);
    printf ("0\n"); }
}

// all unit clasues
void atleastall (int* array, int size) {
  for (int i = 0; i < size; i++)
    printf ("%i 0\n", array[i]);
}

int atleastallbutone (int* array, int size, int aux) {
#ifdef PAIRWISE
  for (int i = 0; i < size; i++)
    for (int j = i+1; j < size; j++)
      printf ("%i %i 0\n", array[i], array[j]);

  return aux;
#else
  if (size > 1) {
    printf ("%i %i 0\n", array[0], array[1]); }

  if (size > 2) {
    printf ("%i %i 0\n", array[0], array[2]);
    printf ("%i %i 0\n", array[1], array[2]); }

  if (size <= 3) return aux;

  if (size == 4) {
    printf ("%i %i 0\n", array[0], array[3]);
    printf ("%i %i 0\n", array[1], array[3]);
    printf ("%i %i 0\n", array[2], array[3]);
    return aux; }

  printf ("%i %i 0\n", aux, array[0]);
  printf ("%i %i 0\n", aux, array[1]);
  printf ("%i %i 0\n", aux, array[2]);
#ifdef DERIVATION
  printf ("%i %i %i %i 0\n", -aux, -array[0], -array[1], -array[2]);
#endif

#ifdef LINEAR
  array[0] = -aux;
  for (int i = 1; i < size - 2; i++)
    array[i] = array[i+2];
#else
  for (int i = 0; i < size - 3; i++)
    array[i] = array[i+3];
  array[size-3] = -aux;
#endif

  aux++;

  return atleastallbutone (array, size - 2, aux);
#endif
}

int derivation (int* array, int size, int aux) {
#ifdef PAIRWISE
  return aux;
#endif
  if (size <= 4) return aux;

  printf ("d %i %i %i %i 0\n", -aux, -array[0], -array[1], -array[2]);

#ifdef LINEAR
  array[0] = -aux;
  for (int i = 1; i < size - 2; i++)
    array[i] = array[i+2];
#else
  for (int i = 0; i < size - 3; i++)
    array[i] = array[i+3];
  array[size-3] = -aux;
#endif

  aux++;

  return derivation (array, size - 2, aux);
}

int atleastk (int *array, int size, int bound, int start) {
  // horizontal implications and increment implications
  for (int i = 0; i < bound; i++)
    for (int j = i; j <= size - bound + i; j++) {
      printf ("%i ", array[j]);
      if (j > i) printf ("%i ", start + (size-bound-1) * i + j - 1);
      if (j + 1 <= size - bound + i) printf ("-%i ", start + (size-bound-1) * i + j);
      printf ("0\n"); }

  // diagonal implications
  for (int i = 0; i < bound - 1; i++)
    for (int j = i; j < size - bound + i; j++)
      printf("%i -%i 0\n", start + (size-bound-1) * i + j, start + (size-bound-1) * (i+1) + j + 1);

  return start + (size-bound) * bound;
}

int main (int argc, char** argv) {
  if (argc <= 1) {
    printf ("c run using %s FILE.knf\n", argv[0]);
    exit (0); }

  char ch;
  int word_count = 0, in_word = 0, line_count = 0;

  FILE* fp = fopen (argv[1], "r");
  if (fp == NULL) {
    printf("Could not open the file %s\n", argv[1]);
    return 1; }

  while ((ch = fgetc(fp)) != EOF) {
    if (ch == ' ' || ch == '\t' || ch == '\0' || ch == '\n') {
      if (in_word) { in_word = 0; word_count++; }
      if (ch == '\0' || ch == '\n') line_count++; }
    else in_word = 1; }
  fclose (fp);

//  printf ("word count %i\n", word_count);
//  exit (0);

  FILE* input = fopen (argv[1], "r");

  int tmp;
  char c = 0;
  while (1) {
    tmp = fscanf (input, " c%c", &c);
    if (tmp == EOF) return 0;
    if (tmp ==   0) break;
    while (1) {
      if (tmp == EOF ) return 0;
      if (c   == '\n') break;
      tmp = fscanf (input, "%c", &c); } }

  int  nVar = 0, nCls = 0;
  tmp = fscanf (input, " p knf %i %i ", &nVar, &nCls);

  int*  table  = (int* ) malloc (sizeof(int ) * (word_count + line_count));
  int** clause = (int**) malloc (sizeof(int*) * word_count);

  int tsize = 0;
  int parsed = 0;
  int first = 1;
  clause[parsed] = table;
  while (parsed < nCls) {
    int lit;
    if (first) {
      // parse comment
      while (1) {
        tmp = fscanf (input, " c%c", &c);
        if (tmp == EOF) return 0;
        if (tmp ==   0) break;
        while (1) {
          if (tmp == EOF ) return 0;
          if (c   == '\n') break;
          tmp = fscanf (input, "%c", &c); } }

      tmp = fscanf (input, " k %i ", &lit);
      if (tmp == 1) table[tsize++] = lit;
      else          table[tsize++] = 1;
      first = 0;
    }
    else {
      tmp = fscanf (input, " %i ", &lit);
      assert (tmp == 1);
      table[tsize++] = lit;
      if (lit == 0) {
        clause[++parsed] = table + tsize;
        first = 1;
      }
    }
  }
  fclose (input);

  int mVar = 0;
  int mCls = 0;
  int clsSub = 0;

  for (int i = 0; i < nCls; i++) {
    int k = clause[i][0];
    int size = 0;
    int* c = clause[i] + 1;
    while (*c++) size++;
    if      (k   ==    1) {
#ifdef KONLY
      clsSub +=1;
#endif
      continue;
      
    }
    else if (k   ==    2) mCls += size - 1;
    else if (k   == size) mCls += size - 1;
    else if (k+1 == size) {
#ifdef PAIRWISE
      mCls += size * (size-1) / 2 - 1;
#else
      mVar += (size - 1) / 2;
      mCls += (size - 2) * 3 - 1;
#endif
    }
    else {
      mVar += (size-k) * k;
      mCls += (size-k+1)*k + (size-k)*(k-1) - 1;
    }
  }

#ifndef DERIVATION
 #ifdef CNFPLUS
  printf ("p cnf+ %i %i\n", nVar, nCls);
 #else
  printf ("p cnf %i %i\n", nVar + mVar, nCls + mCls -clsSub);
 #endif
#endif

  int aux = nVar + 1;
  for (int i = 0; i < nCls; i++) {
    int k = clause[i][0];
    int size = 0;
    int* c = clause[i] + 1;
    while (*c++) size++;
#ifdef DERIVATION
    int* copy = malloc (sizeof(int) * (size+1));
    for (int j = 0; j <= size; j++)
      copy[j] = clause[i][j];
#endif

#ifdef CNFPLUS
    if (k ==    1) atleastone (clause[i] + 1, size);
    else {
      c = clause[i] + 1;
      while (*c) printf ("%i ", *c++);
      printf (">= %i\n", k);
    }
#else
    if      (k ==    1) {
    #ifndef KONLY
      atleastone (clause[i] + 1, size);
    #endif
      ;
    }
    else if (k ==    2) atleasttwo (clause[i] + 1, size);
    else if (k == size) atleastall (clause[i] + 1, size);
    else if (k + 1 == size) {
      int auxin = aux;
      aux = atleastallbutone (clause[i] + 1, size, aux);
#ifdef DERIVATION
      derivation (copy + 1, size, auxin);
#endif
    }
    else {
      aux = atleastk (clause[i] + 1, size, k, aux); }
#endif
  }
}
