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

// defs
// static int matchTempOpConst(T_exp root, T_binOp op) {
//     bool isPlus = root && root->kind == T_BINOP && root->u.BINOP.op == op;
//     bool tempAndConst =
//         root->u.BINOP.left && root->u.BINOP.left->kind == T_CONST &&
//         root->u.BINOP.right && root->u.BINOP.right->kind == T_TEMP;
//     tempAndConst |= root->u.BINOP.left && root->u.BINOP.left->kind == T_TEMP
//     &&
//                     root->u.BINOP.right && root->u.BINOP.right->kind ==
//                     T_CONST;
//     return isPlus && tempAndConst;
// }

// static bool matchMemStm(T_exp root) {
//     bool isMem = root && root->kind == T_MEM;
//     T_exp memExp = root->u.MEM;
//     bool isBase = memExp->kind == T_Const;
//     bool isBaseIdxWithTemp = memExp->kind == T_BINOP && memExp->u.BINOP.left
//     &&
//                              memExp->u.BINOP.left->kind == T_TEMP &&
//                              memExp->u.BINOP.right &&
//                              memExp->u.BINOP.right->kind == T_TEMP;
//     bool isBaseIdxWithTempAndConst = matchTempOpConst(memExp, T_plus);
// }

// static bool matchMoveConstStm(T_stm root) {
//     bool isMove = root->kind == T_MOVE;
//     // bool isConst = root->u
//     // .MOVE.
// }

// static bool matchMoveTemp2Temp(T_stm root) {
//     return root->u.MOVE.dst && root->u.MOVE.dst->kind == T_TEMP &&
//            root->u.MOVE.src && root->u.MOVE.src->kind == T_TEMP;
// }

// // Move Mem to Temp
// static bool matchMoveMem2Temp(T_stm root) {}

// // Match binary operations expression
// static bool matchBinOpExp(T_exp root) {
//     //    return root->u.BINOP.
// }

static void munchStm(T_stm stm) {
    switch (stm->kind) {
        case T_MOVE: {
            T_exp dst = stm->u.MOVE.dst;
            T_exp src = stm->u.MOVE.src;
            if (dst->kind == T_TEMP && src->kind == T_TEMP) {
                emit(AS_Move("movq `s0, `d0", L(dst->u.TEMP, NULL),
                             L(src->u.TEMP, NULL)));
                return;
            }
            // Move(Mem, Mem)
            if (src->kind == T_MEM && dst->kind == T_MEM) {
                // in x86-64 arch, no direct instruction support
                Temp_temp temp = Temp_newtemp();
                Temp_temp srcAddr = munchExp(src->u.MEM);
                Temp_temp dstAddr = munchExp(dst->u.MEM);
                AS_instr move2Temp =
                    AS_Move("movq (`s0), `d0", L(temp, NULL), L(srcAddr, NULL));
                AS_instr move2Mem =
                    AS_Move("movq `s0, (`d0)", L(dstAddr, NULL), L(temp, NULL));
                emit(move2Temp);
                emit(move2Mem);
                return;
            }
            // mov Imm(%src), %dst
            // Move(Mem ( + (%, CONST)), %)
            if (dst->kind == T_MEM && dst->u.MEM->kind == T_BINOP &&
                dst->u.MEM->u.BINOP.op == T_plus &&
                dst->u.MEM->u.BINOP.left->kind == T_CONST) {
                // Temp_temp src = munchExp(src);
                Temp_temp base = munchExp(dst->u.MEM->u.BINOP.right);
                char buf[_LEN];
                sprintf(buf, "movq %d(`s0), `d0",
                        dst->u.MEM->u.BINOP.left->u.CONST);
                AS_instr instr = AS_Oper(String(buf), L(base, NULL),
                                         L(munchExp(src), NULL), NULL);
                emit(instr);
                return;
            }
            // mov Imm(R), R
            if (src->kind == T_MEM && src->u.MEM->kind == T_BINOP &&
                src->u.MEM->u.BINOP.op == T_plus &&
                src->u.MEM->u.BINOP.right->kind == T_CONST) {
                char buf[100];
                sprintf(buf, "movq %d(`s0), `d0",
                        src->u.MEM->u.BINOP.right->u.CONST);
                emit(AS_Move(String(buf), L(munchExp(src), NULL),
                             L(munchExp(dst), NULL)));
                return;
            }
            // mov Imm, R
            if (src->kind == T_CONST) {
                char buf[_LEN];
                sprintf(buf, "movq %d, `d0", src->u.CONST);
                AS_instr instr =
                    AS_Move(String(buf), L(munchExp(dst), NULL), L(NULL, NULL));
                emit(instr);
                return;
            }
            // Matched: function call
            else if (src->kind == T_CALL && dst->kind == T_TEMP) {
                Temp_temp r = munchExp(src->u.CALL.fun);
                Temp_tempList l = munchArgs(0, src->u.CALL.args);
                Temp_tempList calldefs =
                    L(F_rax(), l);  // return value and args
                emit(AS_Oper("call `s0\n", calldefs, L(r, l), NULL));
                return;
            } else if (dst->kind == T_MEM) {
                Temp_temp val = munchExp(src);
                Temp_temp addr = munchExp(dst->u.MEM);
                emit(AS_Move("movq `s0, (`s0)", L(addr, NULL), L(val, NULL)));
                return;
            }
            if (dst->kind == T_TEMP) {
                Temp_temp val = munchExp(src);
                char buf[_LEN];
                sprintf(buf, "movq `s0, `d0 // 153");
                AS_instr instr =
                    AS_Move(String(buf), L(val, NULL), L(dst->u.TEMP, NULL));
                emit(instr);
                return;
            }
            assert(0);
        }
        case T_EXP: {
            if (stm->u.EXP->kind == T_CALL) {
                // Matched a procedure call
                Temp_temp r = munchExp(stm->u.EXP->u.CALL.fun);
                Temp_tempList args = munchArgs(0, stm->u.EXP->u.CALL.args);
                Temp_tempList calldefs =
                    L(F_rax(), args);  // return value and args
                emit(AS_Oper("call `s0", calldefs, L(r, args), NULL));
                return;
            }
            // munchExp(stm->u.EXP);
            return;
        }
        case T_LABEL: {
            Temp_label label = stm->u.LABEL;
            char buf[512];
            sprintf(buf, "%s", Temp_labelstring(label));
            emit(AS_Label(String(buf), label));
            return;
        }
        case T_JUMP: {
            Temp_label target = stm->u.JUMP.exp->u.NAME;
            emit(AS_Oper("jmp `j0", NULL, NULL,
                         AS_Targets(Temp_LabelList(target, NULL))));
            return;
        }
        case T_CJUMP: {
            Temp_temp src = munchExp(stm->u.CJUMP.left);
            Temp_temp dst = munchExp(stm->u.CJUMP.right);
            T_relOp op = stm->u.CJUMP.op;
            Temp_label trueLabel = stm->u.CJUMP.true;
            Temp_label falseLabel = stm->u.CJUMP.false;
            string cJmp[] = {"je", "jne", "jl", "jg", "jle", "jge"};
            emit(AS_Oper("subq `s0, `d0", L(dst, NULL), L(src, NULL), NULL));
            char buf[_LEN];
            sprintf(buf, "%s %s // cjump", cJmp[op],
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
    switch (exp->kind) {
        case T_BINOP: {
            // Match "op Imm, $dst", op -> + | - | *
            if (exp->u.BINOP.op == T_plus &&
                exp->u.BINOP.right->kind == T_CONST) {
                Temp_temp dst = munchExp(exp->u.BINOP.left);
                char buf[_LEN];
                sprintf(buf, "addq %d, `d0", exp->u.BINOP.right->u.CONST);
                AS_instr instr =
                    AS_Oper(String(buf), L(dst, NULL), L(NULL, NULL), NULL);
                emit(instr);
                return dst;
            } else if (exp->u.BINOP.op == T_minus &&
                       exp->u.BINOP.right->kind == T_CONST) {
                Temp_temp dst = munchExp(exp->u.BINOP.left);
                char buf[_LEN];
                sprintf(buf, "subq $%d, `d0", exp->u.BINOP.right->u.CONST);
                AS_instr instr =
                    AS_Oper(String(buf), L(dst, NULL), L(NULL, NULL), NULL);
                emit(instr);
                return dst;
            } else if (exp->u.BINOP.op == T_minus &&
                       exp->u.BINOP.right->kind == T_CONST) {
                Temp_temp dst = munchExp(exp->u.BINOP.left);
                char buf[_LEN];
                sprintf(buf, "subq %d, `s0", exp->u.BINOP.right->u.CONST);
                AS_instr instr =
                    AS_Oper(String(buf), L(dst, NULL), L(NULL, NULL), NULL);
                emit(instr);
                return dst;
            } else if (exp->u.BINOP.op == T_mul &&
                       exp->u.BINOP.right->kind == T_CONST) {
                Temp_temp dst = munchExp(exp->u.BINOP.left);
                char buf[_LEN];
                sprintf(buf, "imul $%d, `d0", exp->u.BINOP.right->u.CONST);
                AS_instr instr =
                    AS_Oper(String(buf), L(dst, NULL), L(NULL, NULL), NULL);
                emit(instr);
                return dst;
            }
            // Match "idivq $src": %rax(quotient), %rdx(remainder) <- %rdx:%rax
            if (exp->u.BINOP.op == T_div) {
                Temp_temp src = munchExp(exp->u.BINOP.left);
                // Temp_temp dst = munchExp(exp->u.BINOP.right);
                AS_instr movSrc = AS_Move("movq `s0, `d0 // div",
                                          L(F_rax(), NULL), L(src, NULL));
                AS_instr oct =
                    AS_Oper("cqto", L(F_rdx(), L(F_rax(), NULL)),
                            L(F_rax(), NULL), NULL);  // convert to oct word
                AS_instr div =
                    AS_Oper("idivq `s0", L(F_rdx(), L(F_rax(), NULL)),
                            L(F_rdx(), L(F_rax(), NULL)), NULL);
                emit(movSrc);
                emit(oct);
                emit(div);
                return F_rax();
            }
            // Match "op $src, $dst", op -> + | - | * | /
            Temp_temp src = munchExp(exp->u.BINOP.left);
            Temp_temp dst = munchExp(exp->u.BINOP.right);
            char buf[_LEN];
            sprintf(buf, "%s `s0, `d0", opStr[exp->u.BINOP.op]);
            AS_instr instr =
                AS_Oper(String(buf), L(dst, NULL), L(src, L(dst, NULL)), NULL);
            emit(instr);
            return dst;
        }
        case T_MEM: {
            Temp_temp val = Temp_newtemp();
            T_exp mem = exp->u.MEM;
            if (mem->kind == T_CONST) {
                // Match movq Imm, %dst
                char buf[_LEN];
                sprintf(buf, "movq %d, `d0", mem->u.CONST);
                AS_instr instr =
                    AS_Move(String(buf), L(val, NULL), L(NULL, NULL));
                emit(instr);
                return val;
            } else if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus &&
                       mem->u.BINOP.right &&
                       mem->u.BINOP.right->kind == T_CONST) {
                // Matched movq Imm(%src), %dst
                // TODO: the mirror match
                char buf[100];
                sprintf(buf, "movq %d(`s0), `d0", mem->u.BINOP.right->u.CONST);
                emit(AS_Move(String(buf), L(munchExp(mem->u.BINOP.left), NULL),
                             L(val, NULL)));
                return val;
            } else if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus &&
                       mem->u.BINOP.left &&
                       mem->u.BINOP.left->kind == T_CONST) {
                // Matched movq Imm(%src), %dst
                // TODO: the mirror match
                char buf[100];
                sprintf(buf, "movq %d(`s0), `d0",
                        mem->u.MEM->u.BINOP.left->u.CONST);
                emit(AS_Move(String(buf),
                             L(munchExp(mem->u.MEM->u.BINOP.left), NULL),
                             L(val, NULL)));
                return val;
            } else {
                char buf[_LEN];
                sprintf(buf, "movq `s0, `d0 #T_MEM");
                AS_instr instr = AS_Oper(String(buf), L(val, NULL),
                                         L(munchExp(exp->u.MEM), NULL), NULL);
                emit(instr);
                return val;
            }
        }

        case T_NAME: {
            char buf[_LEN];
            sprintf(buf, "movq $%s, `d0", Temp_labelstring(exp->u.NAME));
            Temp_temp r = Temp_newtemp();
            emit(AS_Oper(String(buf), L(r, NULL), L(NULL, NULL), NULL));
            return r;
        }
        case T_TEMP: {
            return exp->u.TEMP;
        }
        case T_CONST: {
            Temp_temp r = Temp_newtemp();
            string buf[_LEN];
            sprintf(buf, "movq $%d, `d0", exp->u.CONST);
            emit(AS_Move(String(buf), L(r, NULL), NULL));
            return r;
        }
        default:
            break;
    }
    assert(0);
}

static Temp_tempList munchArgs(int index, T_expList args) {
    if (args == NULL) return NULL;
    Temp_temp r = munchExp(args->head);
    // x86-64 calling convention: %rdi, %rsi, rdx, rcx, r8, r9
    Temp_temp argsTemp[] = {F_rdi(), F_rsi(), F_rdx(), F_rcx(), F_r8(), F_r9()};
    if (index < 6) {
        // move to corresponding register
        emit(AS_Move("movq `s0, `d0 // call", L(argsTemp[index], NULL),
                     L(r, NULL)));
    } else {
        // push to stack
        emit(AS_Oper("pushq `s0", L(NULL, NULL), L(r, NULL), NULL));
    }
    Temp_tempList next = munchArgs(index + 1, args->tail);
    return L(r, next);
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
    return list;
}
