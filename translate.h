#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "absyn.h"
#include "frame.h"
#include "temp.h"
#include "util.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;
typedef struct Tr_expList_ *Tr_expList;
struct Tr_expList_ {
    Tr_exp head;
    Tr_expList tail;
};
typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;
struct Tr_accessList_ {
    Tr_access head;
    Tr_accessList tail;
};

typedef struct Tr_level_ *Tr_level;

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail);

Tr_expList Tr_ExpListAppend(Tr_expList list, Tr_expList tail);
Tr_expList Tr_ExpListTail(Tr_expList list);

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

Tr_level Tr_outermost(void);

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);

Tr_access Tr_allocLocal(Tr_level level, bool escape);

/* Expressions */
Tr_exp Tr_SimpleVar(Tr_access, Tr_level);
Tr_exp Tr_fieldVar(Tr_exp rec, int nField);
Tr_exp Tr_subscriptVar(Tr_exp array, Tr_exp index);
Tr_exp Tr_intExp(int val);
Tr_exp Tr_nilExp();
Tr_exp Tr_stringExp(string str);
Tr_exp Tr_callExp(Temp_label funcLabel, Tr_expList args, Tr_level caller,
                  Tr_level callee);
Tr_exp Tr_opExp(A_oper op, Tr_exp left, Tr_exp right);
Tr_exp Tr_RecordExp(Tr_expList recList);
Tr_exp Tr_SeqExp(Tr_exp head, Tr_exp tail);
Tr_exp Tr_listToExp(Tr_expList exps);
Tr_exp Tr_EseqExp(Tr_exp list, Tr_exp newChild);
Tr_exp Tr_assignExp(Tr_exp var, Tr_exp val);
Tr_exp Tr_ifThenExp(Tr_exp condTr, Tr_exp thenTr);
Tr_exp Tr_ifThenElseExp(Tr_exp condTr, Tr_exp thenTr, Tr_exp elseTr);
Tr_exp Tr_whileExp(Tr_exp cond, Tr_exp body, Temp_label done);
Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp eleVal);
Tr_exp Tr_breakExp(Temp_label label);
Tr_exp Tr_forExp(Tr_access loopVar, Tr_level varLevel, Tr_exp lo, Tr_exp hi,
                 Tr_exp body, Temp_label done);
Tr_exp Tr_StringCmp(Tr_exp left, Tr_exp right) ;

/* Declarations */
Tr_exp Tr_varDec(Tr_access access, Tr_exp init);
Tr_exp Tr_noOp();

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals);

void Tr_AppendStringFrag(Temp_label label, string str);

F_fragList Tr_getResult();

void printIR();

#endif
