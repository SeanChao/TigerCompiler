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
    U_boolList escapeList;
    F_accessList formals;
    F_accessList localVars;
};

struct F_access_ {
    enum { inFrame, inReg } kind;
    union {
        int offset;     // inFrame
        Temp_temp reg;  // inReg
    } u;
};

Temp_temp F_FP() { return Temp_newtemp(); }
const int F_wordSize = 8;

/* decs */

F_accessList F_AccessList(F_access head, F_accessList tail);

static Temp_temp rax, rbx, rcx, rdx, rdi, rsi, rbp, rsp, r8, r9, r10, r11, r12,
    r13, r14, r15;
// static Temp_tempList callerSaved = Temp_TempList(NULL, NULL);
// static Temp_tempList calleeSaved = Temp_TempList(NULL, NULL);

/* defs */

/**
 * Turn an F_access into the Tree expression
 */
T_exp F_Exp(F_access acc, T_exp framePtr) {
    switch (acc->kind) {
        case inFrame:
            return T_Mem(T_Binop(T_plus, framePtr, T_Const(acc->u.offset)));
        case inReg:
        default:
            break;
    }
    assert(0);
}

static F_access F_AccessInFrame(F_frame frame) {
    F_accessList locals = frame->localVars;
    F_access access = checked_malloc(sizeof(*access));
    access->kind = inFrame;
    int offset = 0;
    while (locals->tail) {
        locals = locals->tail;
        offset -= F_wordSize;
    }
    access->u.offset = offset;
    locals->tail = F_AccessList(access, NULL);
    return access;
}

static F_access F_AccessInReg(Temp_temp reg) {
    F_access access = checked_malloc(sizeof(*access));
    access->kind = inFrame;
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

F_frame F_newFrame(Temp_label name, U_boolList Tr_formals) {
    F_frame frame = checked_malloc(sizeof(*frame));
    frame->name = name;
    frame->escapeList = Tr_formals;
    frame->formals = createAccessList(Tr_formals);
    frame->localVars = createAccessList(Tr_formals);
    return frame;
}

Temp_label F_name(F_frame f) { return f->name; }

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

T_stm F_procEntryExit1(F_frame frame, T_stm stm) { return stm; }

T_exp F_externalCall(string s, T_expList args) {
    return T_Call(T_Name(Temp_namedlabel(s)), args);
}

static Temp_tempList returnSink = NULL;
static Temp_tempList calleeSaves = NULL;

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
        body, AS_InstrList(AS_Oper("// procEntryExit2", NULL, returnSink, NULL),
                           NULL));
}

AS_instrList F_procEntryExit3(F_frame frame, AS_instrList body) {
    char buf[100];
    sprintf(buf, "procedure %s", S_name(frame->name));
    return AS_Proc(String(buf), body, "END");
}

void F_new() {
    rax = Temp_newtemp();
    rbx = Temp_newtemp();
    rcx = Temp_newtemp();
    rdx = Temp_newtemp();
    rdi = Temp_newtemp();
    rsi = Temp_newtemp();
    rbp = Temp_newtemp();
    rsp = Temp_newtemp();
    r8 = Temp_newtemp();
    r9 = Temp_newtemp();
    r10 = Temp_newtemp();
    r11 = Temp_newtemp();
    r12 = Temp_newtemp();
    r13 = Temp_newtemp();
    r14 = Temp_newtemp();
    r15 = Temp_newtemp();
    // RBX, RBP, RDI, RSI, RSP, R12, R13, R14, and R15
    calleeSaves = Temp_TempList(
        rbx,
        Temp_TempList(
            rbp,
            Temp_TempList(
                rdi,
                Temp_TempList(
                    rsi,
                    Temp_TempList(
                        rsp, Temp_TempList(
                                 r12, Temp_TempList(
                                          r13, Temp_TempList(
                                                   r14, Temp_TempList(
                                                            r15, NULL)))))))));
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
