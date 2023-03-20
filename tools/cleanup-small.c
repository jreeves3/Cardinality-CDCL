#include <stdio.h>
#include <stdlib.h>

int *mask, stamp = 0;

int isTautology (int *clause) {
  stamp++;
  while (*clause) {
    if (mask[-*clause] == stamp) return 1;
    mask[*clause] = stamp;
    clause++; }
  return 0; }

int removeDuplicateLiterals (int *clause) {
  stamp++;
  int count = 0;
  int *_clause = clause;
  while (*clause) {
    if (mask[*clause] == stamp) count++;
    else {
      *_clause++ = *clause;
      mask[*clause] = stamp; }
    clause++; }
  *_clause = 0;
  return count; }

void printClause (int *clause) {
  while (*clause)
    printf("%i ", *clause++);
  printf("0\n"); }

int main (int argc, char** argv) {
  FILE* cnf;

  cnf = fopen (argv[1], "r");

  int tmp, lit, nVar, nCls;
  tmp = fscanf (cnf, " p cnf %i %i ", &nVar, &nCls);
  mask = (int*) malloc (sizeof (int) * (2*nVar + 1));
  mask += nVar;

  int size = 0, *table, *cls;
  table = (int*) malloc (sizeof(int) * 100 * nCls);
  cls   = (int*) malloc (sizeof(int) * (nCls+1));
  nCls = 0;

  cls[0] = 0;
  while (1) {
    tmp = fscanf (cnf, " %i ", &lit);
    if (tmp != 1) break;
    table [size++] = lit;
    if (lit == 0) cls[++nCls] = size; }

  int i, j = 0, k;
  for (i = 0; i < nCls; i++) {
    if (isTautology (table + cls[i])) continue;
    removeDuplicateLiterals (table + cls[i]);
    cls[j++] = cls[i]; }
  nCls = j;

  printf("p cnf %i %i\n", nVar, nCls);
  for (i = 0; i < nCls; i++) {
    printClause (table + cls[i]); }

}
