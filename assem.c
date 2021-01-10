/*
 * mipscodegen.c - Functions to translate to Assem-instructions for
 *             the Jouette assembly language using Maximal Munch.
 */

#include "assem.h"
#include <stdio.h>
#include <stdlib.h> /* for atoi */
#include <string.h> /* for strcpy */
#include "absyn.h"
#include "errormsg.h"
#include "frame.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "util.h"

AS_targets AS_Targets(Temp_labelList labels) {
    AS_targets p = checked_malloc(sizeof *p);
    p->labels = labels;
    return p;
}

AS_instr AS_Oper(string a, Temp_tempList d, Temp_tempList s, AS_targets j) {
    AS_instr p = (AS_instr)checked_malloc(sizeof *p);
    p->kind = I_OPER;
    p->u.OPER.assem = a;
    p->u.OPER.dst = d;
    p->u.OPER.src = s;
    p->u.OPER.jumps = j;
    return p;
}

AS_instr AS_Label(string a, Temp_label label) {
    AS_instr p = (AS_instr)checked_malloc(sizeof *p);
    p->kind = I_LABEL;
    p->u.LABEL.assem = a;
    p->u.LABEL.label = label;
    return p;
}

/**
 * Like AS_Oper, but only performs data transfer
 */
AS_instr AS_Move(string a, Temp_tempList d, Temp_tempList s) {
    AS_instr p = (AS_instr)checked_malloc(sizeof *p);
    p->kind = I_MOVE;
    p->u.MOVE.assem = a;
    p->u.MOVE.dst = d;
    p->u.MOVE.src = s;
    return p;
}

AS_instrList AS_InstrList(AS_instr head, AS_instrList tail) {
    AS_instrList p = (AS_instrList)checked_malloc(sizeof *p);
    p->head = head;
    p->tail = tail;
    return p;
}

/* put list b at the end of list a */
AS_instrList AS_splice(AS_instrList a, AS_instrList b) {
    AS_instrList p;
    if (a == NULL) return b;
    for (p = a; p->tail != NULL; p = p->tail)
        ;
    p->tail = b;
    return a;
}

static Temp_temp nthTemp(Temp_tempList list, int i) {
    assert(list);
    if (i == 0)
        return list->head;
    else
        return nthTemp(list->tail, i - 1);
}

static Temp_label nthLabel(Temp_labelList list, int i) {
    assert(list);
    if (i == 0)
        return list->head;
    else
        return nthLabel(list->tail, i - 1);
}

/* first param is string created by this function by reading 'assem' string
 * and replacing `d `s and `j stuff.
 * Last param is function to use to determine what to do with each temp.
 */
static void format(char *result, string assem, Temp_tempList dst,
                   Temp_tempList src, AS_targets jumps, Temp_map m) {
    // fprintf(stdout, "a format: assem=%s, dst=%p, src=%p\n", assem, dst, src);
    char *p;
    int i = 0; /* offset to result string */
    for (p = assem; p && *p != '\0'; p++) {
        if (*p == '`') {
            switch (*(++p)) {
                case 's': {
                    int n = atoi(++p);
                    string s = Temp_look(m, nthTemp(src, n));
                    strcpy(result + i, s);
                    i += strlen(s);
                } break;
                case 'd': {
                    int n = atoi(++p);
                    string s = Temp_look(m, nthTemp(dst, n));
                    strcpy(result + i, s);
                    i += strlen(s);
                } break;
                case 'j':
                    assert(jumps);
                    {
                        int n = atoi(++p);
                        string s = Temp_labelstring(nthLabel(jumps->labels, n));
                        strcpy(result + i, s);
                        i += strlen(s);
                    }
                    break;
                case '`':
                    result[i] = '`';
                    i++;
                    break;
                default:
                    assert(0);
            }
        } else {
            result[i] = *p;
            i++;
        }
    }
    result[i] = '\0';
}

void AS_print(FILE *out, AS_instr i, Temp_map m) {
    char r[200]; /* result */
    switch (i->kind) {
        case I_OPER:
            format(r, i->u.OPER.assem, i->u.OPER.dst, i->u.OPER.src,
                   i->u.OPER.jumps, m);
            fprintf(out, "%s\n", r);
            break;
        case I_LABEL:
            format(r, i->u.LABEL.assem, NULL, NULL, NULL, m);
            fprintf(out, "%s:\n", r);
            /* i->u.LABEL->label); */
            break;
        case I_MOVE: {
            if ((i->u.MOVE.dst == NULL) && (i->u.MOVE.src == NULL)) {
                char *src = strchr(i->u.MOVE.assem, '%');
                if (src != NULL) {
                    char *dst = strchr(src + 1, '%');
                    if (dst != NULL) {
                        // fprintf(out, "src: %s; dst: %s\n", src, dst);
                        if ((src[1] == dst[1]) && (src[2] == dst[2]) &&
                            (src[3] == dst[3]))
                            break;
                    }
                }
            }
            format(r, i->u.MOVE.assem, i->u.MOVE.dst, i->u.MOVE.src, NULL, m);
            fprintf(out, "%s\n", r);
            break;
        }
    }
}

/* c should be COL_color; temporarily it is not */
void AS_printInstrList(FILE *out, AS_instrList iList, Temp_map m) {
    for (; iList; iList = iList->tail) {
        AS_print(out, iList->head, m);
    }
    fprintf(out, "\n");
}

AS_proc AS_Proc(string p, AS_instrList b, string e) {
    AS_proc proc = checked_malloc(sizeof(*proc));
    proc->prolog = p;
    proc->body = b;
    proc->epilog = e;
    return proc;
}

AS_instrList AS_rewrite(AS_instrList iList, Temp_map m) {
    AS_instrList prev = NULL;
    AS_instrList origin = iList;

    for (AS_instrList i = iList; i; i = i->tail) {
        AS_instr instr = i->head;
        if (instr->kind == I_MOVE) {
            Temp_temp src = instr->u.MOVE.src->head;
            Temp_temp dst = instr->u.MOVE.dst->head;
            if (Temp_look(m, src) == Temp_look(m, dst)) {
                if (prev) {
                    prev->tail = i->tail;
                    continue;
                } else {
                    origin = i->tail;
                }
            }
        }
        if (instr->kind == I_OPER &&
            strncmp("jmp", instr->u.OPER.assem, 4) == 0) {
            if (i->tail) {
                AS_instr nInstr = i->tail->head;
                if (nInstr->kind == I_LABEL &&
                    nInstr->u.LABEL.label ==
                        instr->u.OPER.jumps->labels->head) {
                    i = i->tail;
                    if (prev) {
                        prev->tail = i->tail;
                        continue;
                    } else {
                        origin = i->tail;
                    }
                }
            }
        }
        prev = i;
    }
    return origin;
}

AS_instrList AS_rewriteSpill(F_frame f, AS_instrList il, Temp_tempList spills) {
    for (; spills; spills = spills->tail) {
        Temp_temp t = spills->head;
        F_access acc = F_allocLocal(f, TRUE);
        AS_instrList i = il;
        int id = Temp_getnum(t);
        Temp_temp newTemp = Temp_newtemp();
        for (; i; i = i->tail) {
            AS_instr instr = i->head;
            AS_print2(stdout, instr);
            if (instr->kind == I_LABEL) continue;
            Temp_tempList dst = NULL, src = NULL;
            if (instr->kind == I_OPER) {
                dst = instr->u.OPER.dst;
                src = instr->u.OPER.src;
            } else {
                dst = instr->u.MOVE.dst;
                src = instr->u.MOVE.src;
            }
            if (listLook(src, t)) {
                char buf[256];
                sprintf(buf, "movq %d(`s0), `d0 # spill:use%d", F_getOffset(acc),
                        id);
                AS_instr newInstr =
                    AS_Oper(String(buf), Temp_TempList(newTemp, NULL),
                            Temp_TempList(F_FP(), NULL), NULL);
                Temp_tempReplace(src, t, newTemp);
                i->tail = AS_InstrList(i->head, i->tail);
                i->head = newInstr;
                i = i->tail;
            }
            if (listLook(dst, t)) {
                char buf[256];
                sprintf(buf, "movq `s0, %d(`s1) # spill:def%d", F_getOffset(acc),
                        id);
                AS_instr newInstr = AS_Oper(
                    String(buf), NULL,
                    Temp_TempList(newTemp, Temp_TempList(F_FP(), NULL)), NULL);
                Temp_tempReplace(dst, t, newTemp);
                i->tail = AS_InstrList(newInstr, i->tail);
                i = i->tail;
            }
        }
    }
    return il;
}

void AS_print2(FILE *f, AS_instr instr) {
    AS_print(f, instr, Temp_layerMap(F_tempMap, Temp_name()));
}
