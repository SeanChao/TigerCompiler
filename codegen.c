#include "codegen.h"
#include <stdio.h>
#include <stdlib.h>
#include "absyn.h"
#include "assem.h"
#include "errormsg.h"
#include "frame.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "tree.h"
#include "util.h"

#define _LEN 512  // length of instruction string buf

static AS_instrList iList = NULL, last = NULL;

static void munchStm(T_stm stm);
static Temp_temp munchExp(T_exp exp);
/**
 * munchArgs generates code to move all the arguments to their correct
 * positions.
 *
 * @param index Indicate the current call is munching the i-th argument
 * @return A list of all the temporaries that are to be passed to the machine's
 * call instruction
 */
static Temp_tempList munchArgs(int index, T_expList args);
static void emit(AS_instr ins);

static char *opStr[] = {"addq", "subq", "imulq", "idivq"};

Temp_tempList L(Temp_temp head, Temp_tempList tail) {
    return Temp_TempList(head, tail);
}

static void munchStm(T_stm stm) {
    switch (stm->kind) {
        case T_MOVE: {
            T_exp dst = stm->u.MOVE.dst;
            T_exp src = stm->u.MOVE.src;
            char buf[_LEN];
            if (dst->kind == T_TEMP && src->kind == T_TEMP) {
                emit(AS_Move("movq `s0, `d0 # cat", L(dst->u.TEMP, NULL),
                             L(src->u.TEMP, NULL)));
                return;
            } else if (dst->kind == T_TEMP && src->kind == T_BINOP &&
                       src->u.BINOP.op == T_plus &&
                       src->u.BINOP.right->kind == T_CONST) {
                sprintf(buf, "leaq %d(`s0), `d0", src->u.BINOP.right->u.CONST);
                emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL),
                             L(munchExp(src->u.BINOP.left), NULL), NULL));
                return;
            }
            // Move(Mem, Mem)
            if (src->kind == T_MEM && dst->kind == T_MEM) {
                // in x86-64 arch, no direct instruction support
                // Temp_temp temp = Temp_newtemp();
                Temp_temp val = munchExp(src);
                Temp_temp dstAddr = munchExp(dst->u.MEM);
                AS_instr move2Mem = AS_Oper("movq `s0, (`s1) # m2m-2", NULL,
                                            L(val, L(dstAddr, NULL)), NULL);
                emit(move2Mem);
                return;
            }
            if (src->kind == T_MEM && dst->kind == T_MEM) {
                // in x86-64 arch, no direct instruction support
                Temp_temp temp = Temp_newtemp();
                Temp_temp srcAddr = munchExp(src->u.MEM);
                Temp_temp dstAddr = munchExp(dst->u.MEM);
                AS_instr move2Temp =
                    AS_Oper("movq (`s0), `d0 # m2m-1", L(temp, NULL),
                            L(srcAddr, NULL), NULL);
                AS_instr move2Mem = AS_Oper("movq `s0, (`s1) # m2m-2", NULL,
                                            L(temp, L(dstAddr, NULL)), NULL);
                emit(move2Temp);
                emit(move2Mem);
                return;
            }
            // mov Imm(%src), %dst
            // Move(Mem ( + (%, CONST)), %)
            if (src->kind == T_MEM && src->u.MEM->kind == T_BINOP &&
                src->u.MEM->u.BINOP.op == T_plus &&
                src->u.MEM->u.BINOP.right->kind == T_CONST) {
                // Temp_temp src = munchExp(src);
                Temp_temp base = munchExp(src->u.MEM->u.BINOP.left);
                char buf[_LEN];
                sprintf(buf, "movq %d(`s0), `d0 # frodo",
                        src->u.MEM->u.BINOP.right->u.CONST);
                Temp_temp d = munchExp(dst);
                AS_instr instr =
                    AS_Oper(String(buf), L(d, NULL), L(base, NULL), NULL);
                emit(instr);
                return;
            } else if (src->kind == T_CONST && dst->kind == T_MEM &&
                       dst->u.MEM->kind == T_BINOP &&
                       dst->u.MEM->u.BINOP.right &&
                       dst->u.MEM->u.BINOP.right->kind == T_CONST) {
                // movq Imm, Imm(r)
                sprintf(buf, "movq $%d, %d(`s0) # iir", src->u.CONST,
                        dst->u.MEM->u.BINOP.right->u.CONST);
                emit(AS_Oper(String(buf), NULL,
                             L(munchExp(dst->u.MEM->u.BINOP.left), NULL),
                             NULL));
                return;
            } else if (dst->kind == T_MEM && dst->u.MEM->kind == T_BINOP &&
                       dst->u.MEM->u.BINOP.op == T_plus &&
                       dst->u.MEM->u.BINOP.right->kind == T_BINOP &&
                       dst->u.MEM->u.BINOP.right->u.BINOP.right->kind ==
                           T_CONST) {
                // STORE movq s, (base, idx, size)
                sprintf(buf, "movq `s0, (`s1, `s2, %d) # store",
                        dst->u.MEM->u.BINOP.right->u.BINOP.right->u.CONST);
                emit(AS_Oper(
                    String(buf), NULL,
                    L(munchExp(src),
                      L(munchExp(dst->u.MEM->u.BINOP.left),
                        L(munchExp(dst->u.MEM->u.BINOP.right->u.BINOP.left),
                          NULL))),
                    NULL));
                return;
            } else if (dst->kind == T_MEM && dst->u.MEM->kind == T_BINOP &&
                       dst->u.MEM->u.BINOP.op == T_plus &&
                       dst->u.MEM->u.BINOP.right->kind == T_CONST) {
                // Temp_temp src = munchExp(src);
                Temp_temp base = munchExp(dst->u.MEM->u.BINOP.left);
                char buf[_LEN];
                sprintf(buf, "movq `s0, %d(`s1) # wow",
                        dst->u.MEM->u.BINOP.right->u.CONST);
                AS_instr instr = AS_Oper(String(buf), NULL,
                                         L(munchExp(src), L(base, NULL)), NULL);
                emit(instr);
                return;
            }
            // mov Imm(R), R
            if (src->kind == T_MEM && src->u.MEM->kind == T_BINOP &&
                src->u.MEM->u.BINOP.op == T_plus &&
                src->u.MEM->u.BINOP.right->kind == T_CONST) {
                char buf[100];
                sprintf(buf, "movq %d(`s0), `d0 # potter",
                        src->u.MEM->u.BINOP.right->u.CONST);
                emit(AS_Oper(String(buf), L(munchExp(src), NULL),
                             L(munchExp(dst), NULL), NULL));
                return;
            }
            // mov Imm, R
            if (src->kind == T_CONST) {
                char buf[_LEN];
                sprintf(buf, "movq $%d, `d0 # movq imm1", src->u.CONST);
                AS_instr instr =
                    AS_Oper(String(buf), L(munchExp(dst), NULL), NULL, NULL);
                emit(instr);
                return;
            } else if (dst->kind == T_MEM) {
                Temp_temp val = munchExp(src);
                Temp_temp addr = munchExp(dst->u.MEM);
                emit(AS_Oper("movq `s0, (`s1) # magic", NULL,
                             L(val, L(addr, NULL)), NULL));
                return;
            }
            if (dst->kind == T_TEMP) {
                Temp_temp val = munchExp(src);
                char buf[_LEN];
                sprintf(buf, "movq `s0, `d0 # 153");
                AS_instr instr =
                    AS_Move(String(buf), L(dst->u.TEMP, NULL), L(val, NULL));
                emit(instr);
                return;
            }
            assert(0);
        }
        case T_EXP: {
            munchExp(stm->u.EXP);
            return;
        }
        case T_LABEL: {
            Temp_label label = stm->u.LABEL;
            char buf[512];
            sprintf(buf, ".%s", Temp_labelstring(label));
            emit(AS_Label(String(buf), label));
            return;
        }
        case T_JUMP: {
            Temp_label target = stm->u.JUMP.exp->u.NAME;
            emit(AS_Oper("jmp .`j0 # ocean", NULL, NULL,
                         AS_Targets(Temp_LabelList(target, NULL))));
            return;
        }
        case T_CJUMP: {
            // TODO: better be named left/right...
            Temp_temp src = munchExp(stm->u.CJUMP.left);
            Temp_temp dst = munchExp(stm->u.CJUMP.right);
            T_relOp op = stm->u.CJUMP.op;
            Temp_label trueLabel = stm->u.CJUMP.true;
            Temp_label falseLabel = stm->u.CJUMP.false;
            string cJmp[] = {"je", "jne", "jl", "jg", "jle", "jge"};
            // cmq s0, s1: s1 - s0
            emit(AS_Oper("cmp `s0, `s1", NULL, L(dst, L(src, NULL)), NULL));
            char buf[_LEN];
            sprintf(buf, "%s .%s # cjump", cJmp[op],
                    Temp_labelstring(trueLabel));
            emit(AS_Oper(String(buf), NULL, NULL,
                         AS_Targets(Temp_LabelList(
                             trueLabel, Temp_LabelList(falseLabel, NULL)))));
            return;
        }
        default:
            break;
    }
    assert(0);
}

Temp_temp munchExp(T_exp exp) {
    char buf[_LEN];
    switch (exp->kind) {
        case T_BINOP: {
            // Match "op Imm, $dst", op -> + | - | *
            if (exp->u.BINOP.op == T_plus && exp->u.BINOP.right &&
                exp->u.BINOP.right->kind == T_BINOP &&
                exp->u.BINOP.right->u.BINOP.op == T_mul &&
                exp->u.BINOP.right->u.BINOP.right->kind == T_CONST) {
                Temp_temp r = Temp_newtemp();
                Temp_temp s0 = munchExp(exp->u.BINOP.left);
                Temp_temp s1 = munchExp(exp->u.BINOP.right->u.BINOP.left);
                sprintf(buf, "leaq (`s0, `s1, %d), `d0",
                        exp->u.BINOP.right->u.BINOP.right->u.CONST);
                emit(
                    AS_Oper(String(buf), L(r, NULL), L(s0, L(s1, NULL)), NULL));
                return r;
            }
            // side effect addq
            else if (exp->u.BINOP.op == T_plus &&
                     exp->u.BINOP.right->kind == T_CONST) {
                Temp_temp dst = munchExp(exp->u.BINOP.left);
                Temp_temp tmp = Temp_newtemp();
                sprintf(buf, "movq `s0, `d0 # mov4se");
                emit(AS_Move(String(buf), L(tmp, NULL), L(dst, NULL)));
                sprintf(buf, "addq $%d, `d0 # im", exp->u.BINOP.right->u.CONST);
                emit(AS_Oper(String(buf), L(tmp, NULL), L(tmp, NULL), NULL));
                return tmp;
            } else if (exp->u.BINOP.op == T_minus &&
                       exp->u.BINOP.right->kind == T_CONST) {
                Temp_temp dst = munchExp(exp->u.BINOP.left);
                Temp_temp tmp = Temp_newtemp();
                char buf[_LEN];
                sprintf(buf, "movq `s0, `d0 # 4im");
                emit(AS_Move(String(buf), L(tmp, NULL), L(dst, NULL)));
                sprintf(buf, "subq $%d, `d0 # im", exp->u.BINOP.right->u.CONST);
                emit(AS_Oper(String(buf), L(tmp, NULL), L(tmp, NULL), NULL));
                return tmp;
            } else if (exp->u.BINOP.op == T_mul &&
                       exp->u.BINOP.right->kind == T_CONST) {
                Temp_temp dst = munchExp(exp->u.BINOP.left);
                Temp_temp tmp = Temp_newtemp();
                char buf[_LEN];
                sprintf(buf, "movq `s0, `d0 # mov4se");
                emit(AS_Move(String(buf), L(tmp, NULL), L(dst, NULL)));
                sprintf(buf, "imul $%d, `d0 # im", exp->u.BINOP.right->u.CONST);
                AS_instr instr =
                    AS_Oper(String(buf), L(tmp, NULL), L(tmp, NULL), NULL);
                emit(instr);
                return tmp;
            }
            if (exp->u.BINOP.op == T_mul) {
                // imulq S: S * %rax -> %rdx:%rax
                Temp_temp mul1 = munchExp(exp->u.BINOP.left);
                Temp_temp mul2 = munchExp(exp->u.BINOP.right);
                emit(AS_Move("movq `s0, `d0 # imulq", L(F_rax(), NULL),
                             L(mul1, NULL)));
                emit(AS_Oper("imulq `s0 # imulq", L(F_rax(), L(F_rdx(), NULL)),
                             L(mul2, L(F_rax(), NULL)), NULL));
                return F_rax();
            }
            // idivq $src: %rax(quotient), %rdx(remainder) <- %rdx:%rax // $src
            if (exp->u.BINOP.op == T_div) {
                Temp_temp src = munchExp(exp->u.BINOP.left);
                Temp_temp dst = munchExp(exp->u.BINOP.right);
                AS_instr movSrc = AS_Move("movq `s0, `d0 # div",
                                          L(F_rax(), NULL), L(src, NULL));
                AS_instr oct =
                    AS_Oper("cqto", L(F_rdx(), L(F_rax(), NULL)),
                            L(F_rax(), NULL), NULL);  // convert to oct word
                AS_instr div =
                    AS_Oper("idivq `s0", L(F_rdx(), L(F_rax(), NULL)),
                            L(dst, NULL), NULL);
                emit(movSrc);
                emit(oct);
                emit(div);
                return F_rax();
            }
            // Match "op $src, $dst", op -> + | - | * | /
            // l <-  l op r
            Temp_temp dst = munchExp(exp->u.BINOP.left);
            Temp_temp src = munchExp(exp->u.BINOP.right);
            Temp_temp tmp = Temp_newtemp();
            sprintf(buf, "movq `s0, `d0 # last mov4se");
            emit(AS_Move(String(buf), L(tmp, NULL), L(dst, NULL)));
            sprintf(buf, "%s `s0, `d0 # last match", opStr[exp->u.BINOP.op]);
            emit(
                AS_Oper(String(buf), L(tmp, NULL), L(src, L(tmp, NULL)), NULL));
            return tmp;
        }
        case T_MEM: {
            Temp_temp val = Temp_newtemp();
            T_exp mem = exp->u.MEM;
            char buf[_LEN];
            if (mem->kind == T_CONST) {
                // Match movq Imm, %dst
                char buf[_LEN];
                sprintf(buf, "movq $%d, `d0 # cafe", mem->u.CONST);
                AS_instr instr = AS_Oper(String(buf), L(val, NULL), NULL, NULL);
                emit(instr);
                return val;
            } else if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus &&
                       mem->u.BINOP.right &&
                       mem->u.BINOP.right->kind == T_BINOP &&
                       mem->u.BINOP.right->u.BINOP.right->kind == T_CONST) {
                sprintf(buf, "movq (`s0, `s1, %d), `d0 # arr",
                        mem->u.BINOP.right->u.BINOP.right->u.CONST);
                emit(AS_Oper(
                    String(buf), L(val, NULL),
                    L(munchExp(mem->u.BINOP.left),
                      L(munchExp(mem->u.BINOP.right->u.BINOP.left), NULL)),
                    NULL));
                return val;
            } else if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus &&
                       mem->u.BINOP.left &&
                       mem->u.BINOP.left->kind == T_CONST) {
                // Matched movq Imm(%src), %dst
                char buf[100];
                sprintf(buf, "movq %d(`s0), `d0 # movq2 const-l",
                        mem->u.BINOP.left->u.CONST);
                emit(AS_Oper(String(buf), L(val, NULL),
                             L(munchExp(mem->u.BINOP.right), NULL), NULL));
                return val;
            } else if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus &&
                       mem->u.BINOP.right &&
                       mem->u.BINOP.right->kind == T_CONST) {
                // Matched movq Imm(%src), %dst
                char buf[100];
                sprintf(buf, "movq %d(`s0), `d0 # movq2",
                        mem->u.BINOP.right->u.CONST);
                emit(AS_Oper(String(buf), L(val, NULL),
                             L(munchExp(mem->u.BINOP.left), NULL), NULL));
                return val;
            } else if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus &&
                       mem->u.BINOP.left &&
                       mem->u.BINOP.left->kind == T_CONST) {
                // Matched movq Imm(%src), %dst
                char buf[100];
                sprintf(buf, "movq %d(`s0), `d0 # apple",
                        mem->u.MEM->u.BINOP.left->u.CONST);
                emit(AS_Oper(String(buf),
                             L(munchExp(mem->u.MEM->u.BINOP.right), NULL),
                             L(val, NULL), NULL));
                return val;
            } else if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus &&
                       mem->u.BINOP.right &&
                       mem->u.BINOP.right->kind == T_CONST) {
                // Matched movq Imm(%src), %dst
                sprintf(buf, "movq %d(`s0), `d0 # apple",
                        mem->u.MEM->u.BINOP.right->u.CONST);
                emit(AS_Oper(String(buf),
                             L(munchExp(mem->u.MEM->u.BINOP.left), NULL),
                             L(val, NULL), NULL));
                return val;
            } else {
                char buf[_LEN];
                sprintf(buf, "movq (`s0), `d0 # T_MEM default");
                AS_instr instr = AS_Oper(String(buf), L(val, NULL),
                                         L(munchExp(exp->u.MEM), NULL), NULL);
                emit(instr);
                return val;
            }
        }

        case T_NAME: {
            char buf[_LEN];
            sprintf(buf, "leaq .%s(%%rip), `d0", Temp_labelstring(exp->u.NAME));
            Temp_temp r = Temp_newtemp();
            emit(AS_Oper(String(buf), L(r, NULL), NULL, NULL));
            return r;
        }
        case T_TEMP: {
            return exp->u.TEMP;
        }
        case T_CONST: {
            Temp_temp r = Temp_newtemp();
            char buf[_LEN];
            sprintf(buf, "movq $%d, `d0", exp->u.CONST);
            emit(AS_Oper(String(buf), L(r, NULL), NULL, NULL));
            return r;
        }
        case T_CALL: {
            Temp_temp r = F_Rv();
            Temp_tempList argsTemp = munchArgs(0, exp->u.CALL.args);
            sprintf(buf, "call %s", Temp_labelstring(exp->u.CALL.fun->u.NAME));
            emit(AS_Oper(String(buf),
                         Temp_TempList(F_Rv(), F_callerSavedRegisters()),
                         argsTemp, NULL));
            return r;
        }
        default:
            break;
    }
    assert(0);
}

/**
 * Put args to proper locations for the callee
 */
static Temp_tempList munchArgs(int index, T_expList args) {
    if (args == NULL) return NULL;
    Temp_temp r = munchExp(args->head);
    // x86-64 calling convention: %rdi, %rsi, rdx, rcx, r8, r9
    Temp_temp argsTemp[] = {F_rdi(), F_rsi(), F_rdx(), F_rcx(), F_r8(), F_r9()};
    // if (index == 0) {
    //     emit(AS_Oper("pushq `s0 # slink", NULL, L(r, NULL), NULL));
    // } else
    if (index < 6) {
        // move to corresponding register
        emit(AS_Move("movq `s0, `d0 # call param", L(argsTemp[index], NULL),
                     L(r, NULL)));
    } else {
        // push to stack
        emit(AS_Oper("pushq `s0", NULL, L(r, NULL), NULL));
    }
    Temp_tempList next = munchArgs(index + 1, args->tail);
    return index < 6 ? L(argsTemp[index], next) : NULL;
}

static void emit(AS_instr ins) {
    if (last != NULL)
        last = last->tail = AS_InstrList(ins, NULL);
    else
        last = iList = AS_InstrList(ins, NULL);
}

/**
 * Translate IR tree into Assem data structure with "Maximal Munch"
 */
AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    AS_instrList list;
    for (T_stmList sl = stmList; sl; sl = sl->tail) {
        munchStm(sl->head);
    }
    list = iList;
    iList = last = NULL;
    return F_procEntryExit2(list);
}
