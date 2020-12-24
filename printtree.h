#ifndef PRINT_TREE_H
#define PRINT_TREE_H

#include <stdio.h>
#include "tree.h"

/* function prototype from printtree.c */
void printStmList(FILE *out, T_stmList stmList);

void printStmListToDot(FILE *out);

#endif
