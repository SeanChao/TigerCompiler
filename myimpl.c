#include <stdio.h>
#include <string.h>

#include "prog1.h"
#define _MAX(a, b) ((a) > (b) ? (a) : (b))

int maxargs(A_stm stm);

int len_expList(A_expList exps) {
    switch (exps->kind) {
        case A_pairExpList:
            return 1 + len_expList(exps->u.pair.tail);
        case A_lastExpList:
            return 1;
        default:
            break;
    }
    return 0;
}

int maxargs_in_exp(A_exp exp) {
    switch (exp->kind) {
        case A_idExp:
        case A_numExp:
            // idExp and numExp can't contain any printStm
            break;
        case A_opExp: {
            int l = maxargs_in_exp(exp->u.op.left);
            int r = maxargs_in_exp(exp->u.op.right);
            return _MAX(l, r);
        }
        case A_eseqExp: {
            int s = maxargs(exp->u.eseq.stm);
            int e = maxargs_in_exp(exp->u.eseq.exp);
            return _MAX(s, e);
        }
        default:
            break;
    }
    return 0;
}

// maxargs returns the maximum number of arguments of any print statement within
// any subexpression of a given statement.
int maxargs(A_stm stm) {
    int max = 0;
    switch (stm->kind) {
        case A_compoundStm: {
            int l = maxargs(stm->u.compound.stm1);
            int r = maxargs(stm->u.compound.stm2);
            return _MAX(l, r);
        }
        case A_assignStm:
            return maxargs_in_exp(stm->u.assign.exp);
        case A_printStm: {
            // count the length of expList
            int len = len_expList(stm->u.print.exps);
            max = len > max ? len : max;
        }
        default:
            break;
    }
    return max;
}

// A symbol table mapping identifiers to integer values
typedef struct table *Table_;
struct table {
    string id;
    int value;
    Table_ tail;
};

// Create a new Table entry
Table_ Table(string id, int value, struct table *tail) {
    Table_ t = checked_malloc(sizeof(*t));
    t->id = id;
    t->value = value;
    t->tail = tail;
    return t;
}

Table_ interpStm(A_stm stm, Table_ tab);

Table_ update(Table_ t, string key, int val) { return Table(key, val, t); }

int lookup(Table_ t, string key) {
    Table_ cur = t;
    while (cur) {
        if (strcmp(cur->id, key) == 0) {
            return cur->value;
        }
        cur = cur->tail;
    }
}
struct IntAndTable {
    int i;
    Table_ t;
};

struct IntAndTable interpExp(A_exp e, Table_ t) {
    Table_ table = t;
    switch (e->kind) {
        case A_idExp: {
            struct IntAndTable iat;
            iat.i = lookup(table, e->u.id);
            iat.t = table;
            return iat;
        }
        case A_numExp:
            return (struct IntAndTable){e->u.num, table};
        case A_opExp: {
            struct IntAndTable iat1 = interpExp(e->u.op.left, table);
            int val1 = iat1.i;
            table = iat1.t;
            struct IntAndTable iat2 = interpExp(e->u.op.right, table);
            int val2 = iat2.i;
            table = iat2.t;
            int val = 0;
            switch (e->u.op.oper) {
                case A_plus:
                    val = val1 + val2;
                    break;
                case A_minus:
                    val = val1 - val2;
                    break;
                case A_times:
                    val = val1 * val2;
                    break;
                case A_div:
                    val = val1 / val2;
                    break;
                default:
                    break;
            }
            return (struct IntAndTable){val, table};
        }
        case A_eseqExp:
            table = interpStm(e->u.eseq.stm, table);
            return interpExp(e->u.eseq.exp, table);
        default:
            break;
    }
}

Table_ printExpList(A_expList exps, Table_ tab) {
    Table_ table = tab;
    switch (exps->kind) {
        case A_pairExpList: {
            struct IntAndTable iat1 = interpExp(exps->u.pair.head, table);
            printf("%d ", iat1.i);
            table = iat1.t;
            printExpList(exps->u.pair.tail, table);
            break;
        }
        case A_lastExpList: {
            struct IntAndTable iat = interpExp(exps->u.pair.head, table);
            printf("%d ", iat.i);
            table = iat.t;
            break;
        }
        default:
            break;
    }
    return table;
}

Table_ interpStm(A_stm stm, Table_ tab) {
    Table_ table = tab;
    switch (stm->kind) {
        case A_compoundStm:
            table = interpStm(stm->u.compound.stm1, table);
            table = interpStm(stm->u.compound.stm2, table);
            break;
        case A_assignStm: {
            struct IntAndTable iat = interpExp(stm->u.assign.exp, table);
            table = update(iat.t, stm->u.assign.id, iat.i);
            break;
        }
        case A_printStm:
            table = printExpList(stm->u.print.exps, table);
            printf("\n");
        default:
            break;
    }
    return table;
}

// interprets a program in this language
void interp(A_stm stm) { interpStm(stm, NULL); }
