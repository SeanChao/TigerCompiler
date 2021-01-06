
/*Lab5: This header file is not complete. Please finish it with more
 * definition.*/

#ifndef FRAME_H
#define FRAME_H

#include "assem.h"
#include "tree.h"

typedef struct F_frame_ *F_frame;

typedef struct F_access_ *F_access;
typedef struct F_accessList_ *F_accessList;

int F_getOffset(F_access acc);

struct F_accessList_ {
    F_access head;
    F_accessList tail;
};

F_access F_allocLocal(F_frame frame, bool escape);

F_frame F_newFrame(Temp_label name, U_boolList Tr_formals);
Temp_label F_name(F_frame f);

F_accessList F_formalAccessList(F_frame f);

extern const int F_wordSize;
T_exp F_Exp(F_access acc, T_exp framePtr);

/* declaration for fragments */
typedef struct F_frag_ *F_frag;
struct F_frag_ {
    enum { F_stringFrag, F_procFrag } kind;
    union {
        struct {
            Temp_label label;
            string str;
        } stringg;
        struct {
            T_stm body;
            F_frame frame;
        } proc;
    } u;
};

F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);

typedef struct F_fragList_ *F_fragList;
struct F_fragList_ {
    F_frag head;
    F_fragList tail;
};

F_fragList F_FragList(F_frag head, F_fragList tail);

T_exp F_externalCall(string s, T_expList args);

Temp_map F_tempMap;
Temp_map F_initTempMap(void);



/**
 * Moving incoming formal parameters, saving/restoring callee-save registers
 *
 * @param stm tree of func body
 */
T_stm F_procEntryExit1(F_frame frame, T_stm stm);
AS_instrList F_procEntryExit2(AS_instrList body);
/**
 * Performed after register allocation
 */
AS_proc F_procEntryExit3(F_frame frame, AS_instrList body);

void F_new();

Temp_temp F_rax();
Temp_temp F_rbx();
Temp_temp F_rcx();
Temp_temp F_rdx();
Temp_temp F_rsi();
Temp_temp F_rdi();
Temp_temp F_rbp();
Temp_temp F_rsp();
Temp_temp F_r8();
Temp_temp F_r9();
Temp_temp F_r10();
Temp_temp F_r11();
Temp_temp F_r12();
Temp_temp F_r13();
Temp_temp F_r14();
Temp_temp F_r15();

// Return value register
Temp_temp F_Rv();
Temp_temp F_FP();

Temp_tempList F_registers();
Temp_tempList F_callerSavedRegisters();
Temp_tempList F_paramRegisters();
#endif
