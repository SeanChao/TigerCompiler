#include "translate.h"
#include <stdio.h>
#include <string.h>
#include "absyn.h"
#include "frame.h"
#include "printtree.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "tree.h"
#include "util.h"

// LAB5: you can modify anything you want.

struct Tr_access_ {
    Tr_level level;
    F_access access;
};

struct Tr_accessList_ {
    Tr_access head;
    Tr_accessList tail;
};

struct Tr_level_ {
    F_frame frame;
    Tr_level parent;
};

typedef struct patchList_ *patchList;
struct patchList_ {
    Temp_label *head;
    patchList tail;
};

struct Cx {
    patchList trues;
    patchList falses;
    T_stm stm;
};

struct Tr_exp_ {
    enum { Tr_ex, Tr_nx, Tr_cx } kind;
    union {
        T_exp ex;
        T_stm nx;
        struct Cx cx;
    } u;
};

struct Tr_expList_ {
    Tr_exp head;
    Tr_expList tail;
};
static patchList PatchList(Temp_label *head, patchList tail);

Tr_exp Tr_new();
static Tr_exp Tr_Ex(T_exp ex);
static Tr_exp Tr_Nx(T_stm ex);
static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm);

static T_exp unEx(Tr_exp e);
static T_stm unNx(Tr_exp e);
static struct Cx unCx(Tr_exp e);

void doPatch(patchList tList, Temp_label label);

void appendFrag(F_frag frag);

/* defs */

static Tr_exp Tr_Ex(T_exp ex) {
    Tr_exp exp = Tr_new();
    exp->kind = Tr_ex;
    exp->u.ex = ex;
    return exp;
}

static Tr_exp Tr_Nx(T_stm nx) {
    Tr_exp exp = Tr_new();
    exp->kind = Tr_nx;
    exp->u.nx = nx;
    return exp;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm) {
    Tr_exp exp = Tr_new();
    exp->kind = Tr_cx;
    exp->u.cx.trues = trues;
    exp->u.cx.falses = falses;
    exp->u.cx.stm = stm;
    return exp;
}

static T_exp unEx(Tr_exp e) {
    switch (e->kind) {
        case Tr_ex:
            return e->u.ex;
        case Tr_cx: {
            Temp_temp r = Temp_newtemp();
            Temp_label t = Temp_newlabel(), f = Temp_newlabel();
            doPatch(e->u.cx.trues, t);
            doPatch(e->u.cx.falses, f);
            return T_Eseq(
                T_Move(T_Temp(r), T_Const(1)),
                T_Eseq(
                    e->u.cx.stm,
                    T_Eseq(T_Label(f), T_Eseq(T_Move(T_Temp(r), T_Const(0)),
                                              T_Eseq(T_Label(t), T_Temp(r))))));
        }
        case Tr_nx:
            return T_Eseq(e->u.nx, T_Const(0));
    }
    assert(0);
}

static T_stm unNx(Tr_exp e) {
    switch (e->kind) {
        case Tr_ex:
            // Optimize: return the statement
            if (e->u.ex->kind == T_ESEQ &&  // e->u.ex->u.ESEQ.exp &&
                e->u.ex->u.ESEQ.exp->kind == T_CONST &&
                e->u.ex->u.ESEQ.exp->u.CONST == 0)
                return e->u.ex->u.ESEQ.stm;
            return T_Exp(e->u.ex);
        case Tr_nx:
            return e->u.nx;
        case Tr_cx:
            return e->u.cx.stm;
        default:
            break;
    }
    assert(0);
}
static struct Cx unCx(Tr_exp e) {
    struct Cx cx;
    switch (e->kind) {
        case Tr_ex:
            cx.stm = T_Cjump(T_ne, unEx(e), T_Const(0), NULL, NULL);
            cx.trues = PatchList(&cx.stm->u.CJUMP.true, NULL);
            cx.falses = PatchList(&cx.stm->u.CJUMP.false, NULL);
            return cx;
        case Tr_cx:
            return e->u.cx;
    }
    assert(0);
}

static patchList PatchList(Temp_label *head, patchList tail) {
    patchList list;

    list = (patchList)checked_malloc(sizeof(struct patchList_));
    list->head = head;
    list->tail = tail;
    return list;
}

void doPatch(patchList tList, Temp_label label) {
    for (; tList; tList = tList->tail) *(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second) {
    if (!first) return second;
    for (; first->tail; first = first->tail)
        ;
    first->tail = second;
    return first;
}

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail) {
    Tr_expList list = checked_malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;
    return list;
}

Tr_expList Tr_ExpListTail(Tr_expList list) { return list->tail; }

Tr_expList Tr_ExpListAppend(Tr_expList list, Tr_expList tail) {
    list->tail = tail;
    return tail;
}

Tr_level Tr_outermost() {
    Tr_level level = checked_malloc(sizeof(*level));
    return level;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals) {
    // Adds an extra element to the formal parameter list for the static link
    Tr_level level = checked_malloc(sizeof(*level));
    level->frame = F_newFrame(name, U_BoolList(TRUE, formals));
    level->parent = parent;
    return level;
}

Tr_access Tr_allocLocalInReg(Tr_level level) {
    Tr_access access = checked_malloc(sizeof(*access));
    access->level = level;
}

Tr_access Tr_allocLocalInFrame(Tr_level level) {
    F_frame frame = level->frame;
    F_access fAcc = F_allocLocal(level->frame, TRUE);
    Tr_access access = checked_malloc(sizeof(*access));
    access->level = level;
    access->access = fAcc;
    return access;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape) {
    return escape == TRUE ? Tr_allocLocalInFrame(level)
                          : Tr_allocLocalInReg(level);
}

Tr_exp Tr_new() {
    Tr_exp exp = checked_malloc(sizeof(*exp));
    return exp;
}

Tr_exp Tr_SimpleVar(Tr_access access, Tr_level level) {
    // FIXME: fix frame offset
    // Follow static links
    Tr_level decLevel = access->level;
    T_exp exp = T_Temp(F_FP());
    while (level != decLevel) {
        exp = T_Mem(T_Binop(T_plus, exp, T_Const(2 * F_wordSize)));
        level = level->parent;
    }
    exp = F_Exp(access->access, exp);
    return Tr_Ex(exp);
}

Tr_exp Tr_fieldVar(Tr_exp rec, int nField) {
    T_exp field =
        T_Mem(T_Binop(T_plus, unEx(rec), T_Const(nField * F_wordSize)));
    return Tr_Ex(field);
}

Tr_exp Tr_subscriptVar(Tr_exp array, Tr_exp index) {
    return Tr_Ex(
        T_Mem(T_Binop(T_plus, unEx(array),
                      T_Binop(T_mul, unEx(index), T_Const(F_wordSize)))));
}

Tr_exp Tr_nilExp() { return Tr_Ex(T_Const(0)); }

Tr_exp Tr_intExp(int val) { return Tr_Ex(T_Const(val)); }

Tr_exp Tr_stringExp(string str) {
    Temp_label label = Temp_newlabel();
    F_frag frag = F_StringFrag(label, str);
    appendFrag(frag);
    return Tr_Ex(T_Name(label));
}

Tr_exp Tr_callExp(Temp_label funcLabel, Tr_expList args) {
    T_expList argStm = T_ExpList(NULL, NULL);
    T_expList last = argStm;
    Tr_expList cur = args;
    while (cur) {
        last = last->tail = T_ExpList(unEx(cur->head), NULL);
        cur = cur->tail;
    }
    T_exp exp = T_Call(T_Name(funcLabel), argStm->tail);
    return Tr_Ex(exp);
}

Tr_exp Tr_opExp(A_oper op, Tr_exp left, Tr_exp right) {
    static T_relOp opTable[] = {0, 1, 2, 3, 4, 5, T_lt, T_le, T_gt, T_ge};
    T_binOp binOp;
    switch (op) {
        case A_plusOp:
            binOp = T_plus;
        case A_minusOp:
            binOp = T_minus;
        case A_timesOp:
            binOp = T_mul;
        case A_divideOp: {
            binOp = T_div;
            T_exp exp = T_Binop(op, unEx(left), unEx(right));
            return Tr_Ex(exp);
        }
        case A_eqOp:
        case A_leOp:
        case A_geOp:
        case A_ltOp:
        case A_gtOp: {
            T_relOp tOp = opTable[op];
            T_stm stm = T_Cjump(tOp, unEx(left), unEx(right), NULL, NULL);
            patchList trues = PatchList(&stm->u.CJUMP.true, NULL);
            patchList falses = PatchList(&stm->u.CJUMP.false, NULL);
            return Tr_Cx(trues, falses, stm);
        }
        default:
            break;
    }
    printf("impl Tr_op!\n");
    assert(0);
}

Tr_exp Tr_RecordExp(Tr_expList recList) {
    T_stm stm = T_Seq(NULL, NULL);
    Tr_expList cur = recList;
    int size = 0;  // number of fields in the record
    Temp_temp recTemp =
        Temp_newtemp();  // Temp: address of memory for the record
    T_stm init = T_Seq(NULL, NULL);
    T_stm last = init;
    while (cur) {
        last = last->u.SEQ.right =
            T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(recTemp),
                                       T_Const(size * F_wordSize))),
                         unEx(cur->head)),
                  T_Exp(T_Const(114)));
        size++;
        cur = cur->tail;
    }
    stm->u.SEQ.right = init->u.SEQ.right;
    // Allocate heap memory for the record
    stm->u.SEQ.left = T_Move(
        T_Temp(recTemp), T_Call(T_Name(Temp_namedlabel("malloc")),
                                T_ExpList(T_Const(size * F_wordSize), NULL)));
    return Tr_Nx(stm);
}

Tr_exp Tr_SeqExp(Tr_exp head, Tr_exp tail) {
    // Eliminate unexpected behaviors
    if (tail == NULL) return head;
    T_exp seq = T_Eseq(unNx(head), unEx(tail));
    return Tr_Ex(seq);
}

Tr_exp Tr_EseqExp(Tr_exp list, Tr_exp newChild) {
    if (newChild == NULL) return Tr_Ex(T_Eseq(unNx(list), NULL));
    T_exp eseqPtr = list->u.ex;
    while (eseqPtr->u.ESEQ.exp) {
        eseqPtr = eseqPtr->u.ESEQ.exp;
    }
    eseqPtr->u.ESEQ.exp = unEx(newChild);
    return list;
}

Tr_exp Tr_assignExp(Tr_exp var, Tr_exp val) {
    T_stm move = T_Move(unEx(var), unEx(val));
    return Tr_Nx(move);
}

Tr_exp Tr_ifThenExp(Tr_exp condTr, Tr_exp thenTr) {
    Temp_label tLabel = Temp_newlabel();
    Temp_label zLabel = Temp_newlabel();
    struct Cx cx = unCx(condTr);
    patchList trues = cx.trues;
    patchList falses = cx.falses;
    doPatch(trues, tLabel);
    doPatch(falses, zLabel);
    T_stm condT = cx.stm;
    T_stm ret =
        T_Seq(condT, T_Seq(T_Label(tLabel),
                           T_Seq(unNx(thenTr), T_Seq(T_Label(zLabel), NULL))));
    return Tr_Nx(ret);
}

Tr_exp Tr_ifThenElseExp(Tr_exp condTr, Tr_exp thenTr, Tr_exp elseTr) {
    Temp_label tLabel = Temp_newlabel();
    Temp_label fLabel = Temp_newlabel();
    Temp_label zLabel = Temp_newlabel();
    struct Cx cx = unCx(condTr);
    patchList trues = cx.trues;
    patchList falses = cx.falses;
    doPatch(trues, tLabel);
    doPatch(falses, fLabel);
    T_stm condT = cx.stm;
    Temp_temp valueReg = Temp_newtemp();
    T_exp exp = T_Eseq(
        condT,
        T_Eseq(
            T_Label(tLabel),
            T_Eseq(
                T_Move(T_Temp(valueReg), unEx(thenTr)),
                T_Eseq(
                    T_Jump(T_Name(zLabel), Temp_LabelList(zLabel, NULL)),
                    T_Eseq(T_Label(fLabel),
                           T_Eseq(T_Move(T_Temp(valueReg), unEx(elseTr)),
                                  T_Eseq(T_Jump(T_Name(zLabel),
                                                Temp_LabelList(zLabel, NULL)),
                                         T_Eseq(T_Label(zLabel),
                                                T_Temp(valueReg)))))))));
    return Tr_Ex(exp);
}

Tr_exp Tr_whileExp(Tr_exp cond, Tr_exp body) {
    Temp_label test = Temp_newlabel();
    Temp_label done = Temp_newlabel();
    Temp_label loopBody = Temp_newlabel();
    T_Name(test);
    struct Cx cx = unCx(cond);
    doPatch(cx.trues, loopBody);
    doPatch(cx.falses, done);
    T_stm stm = T_Seq(
        T_Label(test),
        T_Seq(cx.stm,
              T_Seq(T_Label(loopBody),
                    T_Seq(unNx(body), T_Seq(T_Jump(T_Name(test),
                                                   Temp_LabelList(test, NULL)),
                                            T_Exp(T_Name(done)))))));
    return Tr_Nx(stm);
}

Tr_exp Tr_forExp(Tr_access loopVar, Tr_level varLevel, Tr_exp lo, Tr_exp hi,
                 Tr_exp body) {
    Tr_exp loopVarTr = Tr_SimpleVar(loopVar, varLevel);
    Tr_exp loopVarExp = Tr_assignExp(loopVarTr, lo);
    T_exp hiTemp = T_Temp(Temp_newtemp());
    Temp_label loopBody = Temp_newlabel();
    Temp_label done = Temp_newlabel();

    T_stm stm = T_Seq(
        T_Move(unEx(loopVarTr), unEx(lo)),
        T_Seq(T_Move(hiTemp, hiTemp),
              T_Seq(T_Cjump(T_gt, unEx(loopVarTr), hiTemp, done, loopBody),
                    T_Seq(T_Label(loopBody),
                          T_Seq(unNx(body),
                                T_Seq(T_Move(unEx(loopVarTr),
                                             T_Binop(T_plus, unEx(loopVarTr),
                                                     T_Const(1))),
                                      T_Seq(T_Cjump(T_le, unEx(loopVarTr),
                                                    hiTemp, loopBody, done),
                                            T_Label(done))))))));

    return Tr_Nx(stm);
}

Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp eleVal) {
    T_exp acc = T_Temp(Temp_newtemp());
    T_exp call = F_externalCall(
        "initArray", T_ExpList(unEx(size), T_ExpList(unEx(eleVal), NULL)));
    return Tr_Nx(T_Move(acc, call));
}

Tr_exp Tr_varDec(Tr_access access, Tr_exp init) {
    T_exp acc = F_Exp(access->access, T_Temp(F_FP()));
    T_exp initTree = unEx(init);
    return Tr_Nx(T_Move(acc, initTree));
}

// Returns no-op
Tr_exp Tr_noOp() { return Tr_Ex(T_Const(0)); }

F_fragList progFragList;
F_fragList last;

void appendFrag(F_frag frag) {
    F_fragList cur = progFragList;
    if (progFragList == NULL) {
        progFragList = F_FragList(frag, NULL);
        last = progFragList;
    } else {
        last = last->tail = F_FragList(frag, NULL);
    }
}

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals) {
    // TODO: if proc is void just unNx()
    T_stm stm = T_Move(T_Temp(Temp_newtemp()), unEx(body));
    F_frag frag = F_ProcFrag(stm, NULL);
    appendFrag(frag);
}

// void Tr_AppendStringFrag(Temp_label label, string str) {
//     F_frag frag = F_StringFrag(label, str);
//     appendFrag(frag);
// }

F_fragList Tr_getResult() { return progFragList; }

static char bin_oper[][12] = {"PLUS", "MINUS",  "TIMES",  "DIVIDE",  "AND",
                              "OR",   "LSHIFT", "RSHIFT", "ARSHIFT", "XOR"};

static char rel_oper[][12] = {"EQ", "NE",  "LT",  "GT",  "LE",
                              "GE", "ULT", "ULE", "UGT", "UGE"};

void pEdge(FILE *out, int pid, int myid) {
    fprintf(out, "%d -> %d;\n", pid, myid);
}

int id() {
    static int counter = 0;
    return ++counter;
}
void printIrStm(FILE *out, T_stm stm, int pid);

void prIrTreeExp(FILE *out, T_exp exp, int pid) {
    int myid = id();
    switch (exp->kind) {
        case T_BINOP:
            fprintf(out, "%d[label=\"BINOP %s\"]\n", myid,
                    bin_oper[exp->u.BINOP.op]);
            pEdge(out, pid, myid);
            prIrTreeExp(out, exp->u.BINOP.left, myid);
            prIrTreeExp(out, exp->u.BINOP.right, myid);
            break;
        case T_MEM:
            fprintf(out, "%d[label=\"MEM\"]\n", myid);
            pEdge(out, pid, myid);
            prIrTreeExp(out, exp->u.MEM, myid);
            break;
        case T_TEMP:
            fprintf(out, "%d[label=\"TEMP t%s\"]\n", myid,
                    Temp_look(Temp_name(), exp->u.TEMP));
            pEdge(out, pid, myid);
            break;
        case T_ESEQ:
            fprintf(out, "%d[label=\"ESEQ\"]\n", myid);
            pEdge(out, pid, myid);
            printIrStm(out, exp->u.ESEQ.stm, myid);
            prIrTreeExp(out, exp->u.ESEQ.exp, myid);
            break;
        case T_NAME:
            fprintf(out, "%d[label=\"NAME %s\"]\n", myid, S_name(exp->u.NAME));
            pEdge(out, pid, myid);
            break;
        case T_CONST:
            fprintf(out, "%d[label=\"CONST %d\"]\n", myid, exp->u.CONST);
            pEdge(out, pid, myid);
            break;
        case T_CALL: {
            T_expList args = exp->u.CALL.args;
            fprintf(out, "%d[label=\"CALL\"]\n", myid);
            pEdge(out, pid, myid);
            prIrTreeExp(out, exp->u.CALL.fun, myid);
            for (; args; args = args->tail) {
                prIrTreeExp(out, args->head, myid);
            }
            break;
        }
    } /* end of switch */
}

void printIrStm(FILE *out, T_stm stm, int pid) {
    int myid = id();
    switch (stm->kind) {
        case T_SEQ:
            fprintf(out, "%d[label=SEQ]\n", myid);
            fprintf(out, "%d -> %d;\n", pid, myid);
            printIrStm(out, stm->u.SEQ.left, myid);
            printIrStm(out, stm->u.SEQ.right, myid);
            break;
        case T_LABEL:
            fprintf(out, "%d[label=\"LABEL %s\"]\n", myid,
                    S_name(stm->u.LABEL));
            pEdge(out, pid, myid);
            break;
        case T_JUMP:
            fprintf(out, "%d[label=JUMP]\n", myid);
            pEdge(out, pid, myid);
            prIrTreeExp(out, stm->u.JUMP.exp, myid);
            break;
        case T_CJUMP:
            fprintf(out, "%d[label=\"CJUMP %s %s %s\"];\n", myid,
                    rel_oper[stm->u.CJUMP.op], S_name(stm->u.CJUMP.true),
                    S_name(stm->u.CJUMP.false));
            pEdge(out, pid, myid);
            prIrTreeExp(out, stm->u.CJUMP.left, myid);
            prIrTreeExp(out, stm->u.CJUMP.right, myid);
            break;
        case T_MOVE:
            fprintf(out, "%d[label=MOVE];\n", myid);
            pEdge(out, pid, myid);
            prIrTreeExp(out, stm->u.MOVE.dst, myid);
            prIrTreeExp(out, stm->u.MOVE.src, myid);
            break;
        case T_EXP:
            fprintf(out, "%d[label=EXP];\n", myid);
            pEdge(out, pid, myid);
            prIrTreeExp(out, stm->u.EXP, myid);
            break;
    }
}

void printIR() {
    F_fragList fragList = Tr_getResult();
    printf("digraph \"IR Tree\"{\n");
    while (fragList) {
        F_frag frag = fragList->head;
        switch (frag->kind) {
            case F_stringFrag: {
                string str = frag->u.stringg.str;
                string label = S_name(frag->u.stringg.label);
                printf("\"%s: %s\"\n", label, str);
                break;
            }
            case F_procFrag: {
                T_stm t = frag->u.proc.body;
                printIrStm(stdout, t, 0);
                // printStmList(stderr, T_StmList(frag->u.proc.body, NULL));
            }
            default:
                break;
        }
        fragList = fragList->tail;
    }
    printf("}\n");
}
