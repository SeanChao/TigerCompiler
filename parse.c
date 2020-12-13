/*
 * parse.c - Parse source file.
 */

#include <stdio.h>
#include <stdlib.h>

#include "absyn.h"
#include "assem.h"
#include "env.h"
#include "errormsg.h"
#include "frame.h"
#include "parse.h"
#include "semant.h"
#include "symbol.h"
#include "temp.h"
#include "translate.h"
#include "tree.h"
#include "types.h"
#include "util.h"

extern int yyparse(void);
extern A_exp absyn_root;

/* parse source file fname;
   return abstract syntax data structure */
A_exp parse(string fname) {
    EM_reset(fname);
    if (yyparse() == 0) /* parsing worked */
        return absyn_root;
    else {
        exit(123);
        return NULL;
    }
}

/*int main(int argc, char **argv) {
 if (argc!=2) {fprintf(stderr,"usage: a.out filename\n"); exit(1);}
 A_exp exp = parse(argv[1]);
 pr_exp(stdout,exp,0);
 SEM_transProg(exp);
 printf("\n");
 return 0;
}*/
