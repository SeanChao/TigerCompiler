/*
 * parse.c - Parse source file.
 */

#include "parse.h"
#include <stdio.h>
#include <stdlib.h>
#include "absyn.h"
#include "errormsg.h"
#include "frame.h"
#include "semant.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "types.h"
#include "util.h"

extern int yyparse(void);
extern void pr_exp(FILE *, A_exp, int);
extern A_exp absyn_root;

/* parse source file fname;
   return abstract syntax data structure */
A_exp parse(string fname) {
    EM_reset(fname);
    if (yyparse() == 0) /* parsing worked */
        return absyn_root;
    else
        return NULL;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: a.out filename\n");
        exit(1);
    }
    // pr_exp(stderr, parse(argv[1]), 0);
    parse(argv[1]);
    // pr_exp(stderr,absyn_root,0);
    if (absyn_root) {
        F_fragList flist = SEM_transProg(absyn_root);
        int k = 0;
        for (; flist; flist = flist->tail) k++;
        fprintf(stderr, "%d\n", k);
    }
    // fprintf(stderr,"\n");
    return 0;
}
