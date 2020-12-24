/*
 * main.c
 */

#include <stdio.h>
#include "absyn.h"
#include "assem.h"
#include "canon.h"
#include "codegen.h"
#include "env.h"
#include "errormsg.h"
#include "escape.h"
#include "frame.h" /* needed by translate.h and printfrags prototype */
#include "parse.h"
#include "prabsyn.h"
#include "printtree.h"
#include "regalloc.h"
#include "semant.h" /* function prototype for transProg */
#include "symbol.h"
#include "temp.h" /* needed by translate.h */
#include "translate.h"
#include "tree.h" /* needed by frame.h */
#include "types.h"
#include "util.h"

extern bool anyErrors;

#define PRINT_IR 1
#define PRINT_LINEARIZED 1
#define PRINT_BLOCK 1
#define PRINT_TRACE 1
#define PRINT_AS 1

/*Lab6: complete the function doProc
 * 1. initialize the F_tempMap
 * 2. initialize the register lists (for register allocation)
 * 3. do register allocation
 * 4. output (print) the assembly code of each function

 * Uncommenting the following printf can help you debugging.*/

Temp_map F_tempMap;

/* print the assembly language instructions to filename.s */
static void doProc(FILE *out, F_frame frame, T_stm body) {
    AS_proc proc;
    struct RA_result allocation;
    T_stmList stmList;
    AS_instrList iList;
    struct C_block blo;

    F_tempMap = Temp_empty();
    F_new();  // Initialize Frame module

#ifdef PRINT_IR
    printf("doProc for function %s:\n", S_name(F_name(frame)));
    printStmList(stdout, T_StmList(body, NULL));
    printf("-------====IR tree=====-----\n");
#endif

    stmList = C_linearize(body);
#ifdef PRINT_LINEARIZED
    printStmList(stdout, stmList);
    printf("-------====Linearlized=====-----\n");
#endif

    blo = C_basicBlocks(stmList);
    C_stmListList stmLists = blo.stmLists;
#ifdef PRINT_BLOCK
    for (; stmLists; stmLists = stmLists->tail) {
        printStmList(stdout, stmLists->head);
        printf("------====Basic block=====-------\n");
    }
#endif

    stmList = C_traceSchedule(blo);
#ifdef PRINT_TRACE
    printStmList(stdout, stmList);
    printf("-------====trace=====-----\n");
#endif
    iList = F_codegen(frame, stmList); /* 9 */

    AS_printInstrList(stdout, iList, Temp_layerMap(F_tempMap, Temp_name()));
    printf("----======before RA=======-----\n");

    // G_graph fg = FG_AssemFlowGraph(iList);  /* 10.1 */
    struct RA_result ra = RA_regAlloc(frame, iList); /* 11 */

    fprintf(out, "BEGIN function\n");
    AS_printInstrList(out, proc->body, Temp_layerMap(F_tempMap, ra.coloring));
    fprintf(out, "END function\n");

    // Part of TA's implementation. Just for reference.
    /*
    AS_rewrite(ra.il, Temp_layerMap(F_tempMap, ra.coloring));
    proc =	F_procEntryExit3(frame, ra.il);

    string procName = S_name(F_name(frame));
    fprintf(out, ".text\n");
    fprintf(out, ".globl %s\n", procName);
    fprintf(out, ".type %s, @function\n", procName);
    fprintf(out, "%s:\n", procName);


    //fprintf(stdout, "%s:\n", Temp_labelstring(F_name(frame)));
    //prologue
    fprintf(out, "%s", proc->prolog);
    AS_printInstrList (out, proc->body,
                          Temp_layerMap(F_tempMap, ra.coloring));
    fprintf(out, "%s", proc->epilog);
    //fprintf(out, "END %s\n\n", Temp_labelstring(F_name(frame)));
    */
}

void doStr(FILE *out, Temp_label label, string str) {
    fprintf(out, ".section .rodata\n");
    fprintf(out, ".%s:\n", S_name(label));

    int length = *(int *)str;
    length = length + 4;
    // it may contains zeros in the middle of string. To keep this work, we need
    // to print all the charactors instead of using fprintf(str)
    fprintf(out, ".string \"");
    int i = 0;
    for (; i < length; i++) {
        fprintf(out, "%c", str[i]);
    }
    fprintf(out, "\"\n");

    // fprintf(out, ".string \"%s\"\n", str);
}

int main(int argc, string *argv) {
    A_exp absyn_root;
    S_table base_env, base_tenv;
    F_fragList frags;
    char outfile[100];
    FILE *out = stdout;

    if (argc == 2) {
        absyn_root = parse(argv[1]);
        if (!absyn_root) return 1;

#if 0
   pr_exp(out, absyn_root, 0); /* print absyn data structure */
   fprintf(out, "\n");
#endif

        // Lab 6: escape analysis
        // If you have implemented escape analysis, uncomment this
        // Esc_findEscape(absyn_root); /* set varDec's escape field */

        frags = SEM_transProg(absyn_root);
        if (anyErrors) return 1; /* don't continue */

        /* convert the filename */
        sprintf(outfile, "%s.s", argv[1]);
        out = fopen(outfile, "w");
        /* Chapter 8, 9, 10, 11 & 12 */
        for (; frags; frags = frags->tail)
            if (frags->head->kind == F_procFrag) {
                doProc(out, frags->head->u.proc.frame,
                       frags->head->u.proc.body);
            } else if (frags->head->kind == F_stringFrag)
                doStr(out, frags->head->u.stringg.label,
                      frags->head->u.stringg.str);

        fclose(out);
        return 0;
    }
    EM_error(0, "usage: %s file.tig", argv[0]);
    return 1;
}