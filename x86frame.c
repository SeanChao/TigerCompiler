#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "assem.h"
#include "frame.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "tree.h"
#include "util.h"

/*Lab5: Your implementation here.*/

// variables

/**
 * Holds information about formal parameters and local variables allocated in
 * this frame.
 */
struct F_frame_ {
    Temp_label name;
    U_boolList escapeList;  // defined by Tr_formals
    F_accessList formals;
    F_accessList localVars;
    int size;
};

struct F_access_ {
    enum { inFrame, inReg } kind;
    union {
        int offset;     // inFrame
        Temp_temp reg;  // inReg
    } u;
};

Temp_temp F_FP();

const int F_wordSize = 8;

int F_getOffset(F_access acc);
/* decs */

int F_getOffset(F_access acc) { return acc->u.offset; }
F_accessList F_AccessList(F_access head, F_accessList tail);

static Temp_temp rax, rbx, rcx, rdx, rdi, rsi, rbp, rsp, r8, r9, r10, r11, r12,
    r13, r14, r15;

static Temp_tempList paramRegisters;
static int paramRegistersNum = 6;

/* defs */

/**
 * Turn an F_access into the Tree expression
 */
T_exp F_Exp(F_access acc, T_exp framePtr) {
    switch (acc->kind) {
        case inFrame:
            return T_Mem(T_Binop(T_plus, framePtr, T_Const(acc->u.offset)));
        case inReg:
            return T_Temp(acc->u.reg);
        default:
            break;
    }
    assert(0);
}

static F_access F_AccessInFrame(F_frame frame) {
    F_accessList locals = frame->localVars;
    F_access access = checked_malloc(sizeof(*access));
    access->kind = inFrame;
    int offset = -(frame->size);
    while (locals->tail) {
        locals = locals->tail;
        // offset -= F_wordSize;
    }
    access->u.offset = offset;
    locals->tail = F_AccessList(access, NULL);
    frame->size += F_wordSize;
    return access;
}

static F_access F_AccessInReg(Temp_temp reg) {
    F_access access = checked_malloc(sizeof(*access));
    access->kind = inReg;
    access->u.reg = reg;
    return access;
}

F_access F_allocLocal(F_frame frame, bool escape) {
    return escape == TRUE ? F_AccessInFrame(frame)
                          : F_AccessInReg(Temp_newtemp());
}

F_accessList F_AccessList(F_access head, F_accessList tail) {
    F_accessList list = checked_malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;
    return list;
}

F_accessList createAccessList(U_boolList formals) {
    U_boolList cur = formals;
    F_access head = F_AccessInReg(Temp_newtemp());
    F_accessList last = F_AccessList(head, NULL);
    F_accessList list = last;
    cur = cur->tail;
    while (cur) {
        last = last->tail = F_AccessList(F_AccessInReg(Temp_newtemp()), NULL);
        cur = cur->tail;
    }
    return list;
}

/**
 * build a new frame, access is created
 */
F_frame F_newFrame(Temp_label name, U_boolList Tr_formals) {
    F_frame frame = checked_malloc(sizeof(*frame));
    frame->name = name;
    frame->escapeList = Tr_formals;
    frame->formals = createAccessList(Tr_formals);
    frame->localVars = createAccessList(Tr_formals);
    frame->size = 0;
    return frame;
}

Temp_label F_name(F_frame f) { return f->name; }

F_accessList F_formalAccessList(F_frame f) { return f->formals; }

F_frag F_StringFrag(Temp_label label, string str) {
    F_frag frag = checked_malloc(sizeof(*frag));
    frag->kind = F_stringFrag;
    frag->u.stringg.label = label;
    frag->u.stringg.str = str;
    return frag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame) {
    F_frag frag = checked_malloc(sizeof(*frag));
    frag->kind = F_procFrag;
    frag->u.proc.body = body;
    frag->u.proc.frame = frame;
    return frag;
}

F_fragList F_FragList(F_frag head, F_fragList tail) {
    F_fragList fragList = checked_malloc(sizeof(*fragList));
    fragList->head = head;
    fragList->tail = tail;
    return fragList;
}

T_exp F_externalCall(string s, T_expList args) {
    return T_Call(T_Name(Temp_namedlabel(s)), args);
}

static Temp_tempList returnSink = NULL;
static Temp_tempList calleeSaves = NULL;
static Temp_tempList callerSaves = NULL;

T_stm F_procEntryExit1(F_frame frame, T_stm stm) {
    // view shift: move temps for formal parameters according to calling
    // convention
    T_stm shift = NULL;
    Temp_tempList paramsTemp = F_paramRegisters();
    int nth = 0;
    for (F_accessList al = frame->formals->tail; al; al = al->tail) {
        F_access acc = al->head;
        T_exp src = NULL, dst = NULL;
        if (acc->kind == inReg && paramsTemp) {
            src = T_Temp(paramsTemp->head);
            dst = F_Exp(acc, T_Temp(F_FP()));
            paramsTemp = paramsTemp->tail;
        } else {
            // push to stack
            // skip 2 words for return addr and saved %rbp
            src = T_Mem(
                T_Binop(T_plus, T_Temp(F_FP()),
                        T_Const((nth - paramRegistersNum + 2) * F_wordSize)));
            dst = F_Exp(acc, T_Temp(F_FP()));
        }
        T_stm stm = T_Move(dst, src);
        shift = shift ? T_Seq(shift, stm) : stm;
        nth++;
    }
    // save/restore callee-save registers, no need for rbp, rsp, handled
    // elsewhere
    Temp_tempList savedTemps = Temp_tempListDiff(
        calleeSaves, Temp_TempList(rbp, Temp_TempList(rsp, NULL)));
    T_stm saveStm = NULL;
    T_stm restoreStm = NULL;
    for (Temp_tempList it = savedTemps; it; it = it->tail) {
        Temp_temp reg = it->head;
        Temp_temp t = Temp_newtemp();
        saveStm = saveStm ? T_Seq(T_Move(T_Temp(t), T_Temp(reg)), saveStm)
                          : T_Move(T_Temp(t), T_Temp(reg));
        restoreStm = restoreStm
                         ? T_Seq(T_Move(T_Temp(reg), T_Temp(t)), restoreStm)
                         : T_Move(T_Temp(reg), T_Temp(t));
    }
    return shift ? T_Seq(saveStm, T_Seq(shift, T_Seq(stm, restoreStm)))
                 : T_Seq(saveStm, T_Seq(stm, restoreStm));
}

/**
 * Appends a sink instruction to the function body to tell the register
 * allocator that certain registers are live at procedure exit.
 * @param body
 * @return
 */
AS_instrList F_procEntryExit2(AS_instrList body) {
    if (!returnSink)
        returnSink =
            Temp_TempList(F_rax(), Temp_TempList(F_rsp(), calleeSaves));
    return AS_splice(
        body, AS_InstrList(AS_Oper("# procEntryExit2", NULL, returnSink, NULL),
                           NULL));
}

AS_proc F_procEntryExit3(F_frame frame, AS_instrList body) {
    // prolog
    char prolog[1024];
    sprintf(prolog, "# procEntryExit3 procedure %s", S_name(frame->name));
    char fmtStr[] =
        "pushq %%rbp\n"
        "movq %%rsp, %%rbp\n"
        "subq $%d, %%rsp\n";
    sprintf(prolog, fmtStr, frame->size);
    // epilog
    char epilog[1024];
    sprintf(epilog, "leaveq\nret\n");
    return AS_Proc(String(prolog), body, String(epilog));
}

void F_new() {
    rax = Temp_newtemp(); // 100
    rbx = Temp_newtemp();
    rcx = Temp_newtemp();
    rdx = Temp_newtemp();
    rdi = Temp_newtemp();
    rsi = Temp_newtemp(); // 105
    rbp = Temp_newtemp();
    rsp = Temp_newtemp();
    r8 = Temp_newtemp();
    r9 = Temp_newtemp();
    r10 = Temp_newtemp(); // 110
    r11 = Temp_newtemp();
    r12 = Temp_newtemp();
    r13 = Temp_newtemp();
    r14 = Temp_newtemp();
    r15 = Temp_newtemp(); // 115
    // RBX, RBP, RDI, RSI, RSP, R12, R13, R14, and R15
    calleeSaves = Temp_TempList(
        rbp,
        Temp_TempList(
            rbx,
            Temp_TempList(
                r12, Temp_TempList(
                         r13, Temp_TempList(r14, Temp_TempList(r15, NULL))))));
    // debug: simpler callee-save
    // calleeSaves = Temp_TempList(rbx, Temp_TempList(rbp, NULL));
    callerSaves = Temp_TempList(
        rax,
        Temp_TempList(
            rcx,
            Temp_TempList(
                rdx,
                Temp_TempList(
                    rdi,
                    Temp_TempList(
                        rsi,
                        Temp_TempList(
                            rsp,
                            Temp_TempList(
                                r8, Temp_TempList(
                                        r9, Temp_TempList(
                                                r10, Temp_TempList(
                                                         r11, NULL))))))))));
    paramRegisters = Temp_TempList(
        rdi,
        Temp_TempList(
            rsi,
            Temp_TempList(
                rdx, Temp_TempList(
                         rcx, Temp_TempList(r8, Temp_TempList(r9, NULL))))));
    F_initTempMap();
}

Temp_temp F_rax() { return rax; }
Temp_temp F_rbx() { return rbx; }
Temp_temp F_rcx() { return rcx; }
Temp_temp F_rdx() { return rdx; }
Temp_temp F_rsi() { return rsi; }
Temp_temp F_rdi() { return rdi; }
Temp_temp F_rbp() { return rbp; }
Temp_temp F_rsp() { return rsp; }
Temp_temp F_r8() { return r8; }
Temp_temp F_r9() { return r9; }
Temp_temp F_r10() { return r10; }
Temp_temp F_r11() { return r11; }
Temp_temp F_r12() { return r12; }
Temp_temp F_r13() { return r13; }
Temp_temp F_r14() { return r14; }
Temp_temp F_r15() { return r15; }
Temp_temp F_Rv() { return rax; }
Temp_temp F_FP() { return rbp; }

Temp_tempList F_registers() {
    return Temp_TempList(
        rax,
        Temp_TempList(
            rbx,
            Temp_TempList(
                rcx,
                Temp_TempList(
                    rdx,
                    Temp_TempList(
                        rbp,
                        Temp_TempList(
                            rdi,
                            Temp_TempList(
                                rsi,
                                Temp_TempList(
                                    rsp,
                                    Temp_TempList(
                                        r8,
                                        Temp_TempList(
                                            r9,
                                            Temp_TempList(
                                                r10,
                                                Temp_TempList(
                                                    r11,
                                                    Temp_TempList(
                                                        r12,
                                                        Temp_TempList(
                                                            r13,
                                                            Temp_TempList(
                                                                r14,
                                                                Temp_TempList(
                                                                    r15,
                                                                    NULL))))))))))))))));
}

Temp_tempList F_callerSavedRegisters() { return callerSaves; }

Temp_tempList F_paramRegisters() { return paramRegisters; }

Temp_map F_initTempMap(void) {
    if (!F_tempMap) {
        F_tempMap = Temp_empty();
        Temp_enter(F_tempMap, F_rax(), "\%rax");
        Temp_enter(F_tempMap, F_rbx(), "\%rbx");
        Temp_enter(F_tempMap, F_rcx(), "\%rcx");
        Temp_enter(F_tempMap, F_rdx(), "\%rdx");
        Temp_enter(F_tempMap, F_rbp(), "\%rbp");
        Temp_enter(F_tempMap, F_rsp(), "\%rsp");
        Temp_enter(F_tempMap, F_rdi(), "\%rdi");
        Temp_enter(F_tempMap, F_rsi(), "\%rsi");
        Temp_enter(F_tempMap, F_r8(), "\%r8");
        Temp_enter(F_tempMap, F_r9(), "\%r9");
        Temp_enter(F_tempMap, F_r10(), "\%r10");
        Temp_enter(F_tempMap, F_r11(), "\%r11");
        Temp_enter(F_tempMap, F_r12(), "\%r12");
        Temp_enter(F_tempMap, F_r13(), "\%r13");
        Temp_enter(F_tempMap, F_r14(), "\%r14");
        Temp_enter(F_tempMap, F_r15(), "\%r15");
    }
    return F_tempMap;
}