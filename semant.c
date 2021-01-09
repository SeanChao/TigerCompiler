#include <assert.h>
#include <stdio.h>
#include <string.h>

#include "util.h"

#include "errormsg.h"

#include "symbol.h"

#include "absyn.h"

#include "types.h"

#include "env.h"

#include "semant.h"

#include "helper.h"

#include "translate.h"

/*Lab5: Your implementation of lab5.*/

struct expty {
    Tr_exp exp;
    Ty_ty ty;
};

// In Lab4, the first argument exp should always be **NULL**.

// S_symbol not defined in symbol.h
struct S_symbol_ {
    string name;
    S_symbol next;
};

// Debug helper
void show_var(S_symbol sym, void* binding) { printf("%s \n", sym->name); }

void show_venv(S_table venv) { S_dump(venv, show_var); }

void show_type(S_symbol sym, void* val) {
    Ty_ty ty = (Ty_ty)val;
    if (ty)
        printf("%s\t-> %d\n", sym->name, ty->kind);
    else
        printf("%s <nil>\n", sym->name);
}

void show_tenv(S_table tenv) { S_dump(tenv, show_type); }

/**
 * Turn "name type" into actual types (A Ty_ty that is not a name)
 * Typically used in `transVar`
 */
Ty_ty actual_ty(Ty_ty t) {
    Ty_ty ty = t;
    while (ty->kind == Ty_name) {
        ty = ty->u.name.ty;
    }
    return ty;
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params);

struct expty expTy(Tr_exp exp, Ty_ty ty) {
    struct expty e;

    e.exp = exp;
    e.ty = ty;

    return e;
}

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level level,
                      Temp_label label) {
    switch (v->kind) {
        case A_simpleVar: {
            E_enventry x = S_look(venv, v->u.simple);
            if (x && x->kind == E_varEntry)
                return expTy(Tr_SimpleVar(x->u.var.access, level),
                             actual_ty(x->u.var.ty));
            else {
                EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
                // show_venv(venv);
            }
            return expTy(NULL, Ty_Int());
        }
        case A_fieldVar: {
            A_var rec = v->u.field.var;          // record name
            S_symbol refField = v->u.field.sym;  // record->field
            struct expty recExpTy = transVar(venv, tenv, rec, level, label);
            if (recExpTy.ty->kind != Ty_record)
                EM_error(v->pos, "not a record type");
            Ty_fieldList fields = recExpTy.ty->u.record;
            int nField = 0;
            while (fields) {
                Ty_field field = fields->head;
                if (refField == field->name) {
                    Tr_exp tr = Tr_fieldVar(recExpTy.exp, nField);
                    return expTy(tr, field->ty);
                }
                fields = fields->tail;
                nField++;
            }
            EM_error(v->pos, "field %s doesn't exist", refField->name);
        }
        case A_subscriptVar: {
            A_var var = v->u.subscript.var;
            // E_enventry varEnt = S_look(venv, var->u.simple);
            struct expty arr = transVar(venv, tenv, var, level, label);
            Ty_ty arrActualTy = actual_ty(arr.ty);
            if (arrActualTy->kind != Ty_array) {
                EM_error(v->pos, "array type required");
                return expTy(NULL, Ty_Nil());
            }
            struct expty idx =
                transExp(venv, tenv, v->u.subscript.exp, level, label);
            if (idx.ty->kind != Ty_int) {
                EM_error(v->pos, "arr indx");
            }
            return expTy(Tr_subscriptVar(arr.exp, idx.exp),
                         actual_ty(arrActualTy->u.array));
        }
        default:
            assert(0);
            break;
    }
    assert(0);
}

/**
 * process an expression
 * level: current level
 */
struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level level,
                      Temp_label label) {
    switch (a->kind) {
        case A_varExp: {
            return transVar(venv, tenv, a->u.var, level, label);
        }
        case A_nilExp:
            return expTy(Tr_nilExp(), Ty_Nil());
        case A_intExp: {
            Tr_exp tr = Tr_intExp(a->u.intt);
            return expTy(tr, Ty_Int());
        }
        case A_stringExp: {
            Tr_exp tr = Tr_stringExp(a->u.stringg);
            return expTy(tr, Ty_String());
        }
        case A_callExp: {
            S_symbol funcName = a->u.call.func;
            E_enventry funcEntry = S_look(venv, funcName);
            // check: function is defined
            if (funcEntry == NULL) {
                EM_error(a->pos, "undefined function %s", funcName->name);
                return expTy(NULL, NULL);
            }
            // check: function arguments
            A_expList args = a->u.call.args;
            Ty_tyList formals = funcEntry->u.fun.formals;
            Tr_expList list = Tr_ExpList(NULL, NULL);
            Tr_expList last = list;
            while (args && formals) {
                struct expty argExpTy =
                    transExp(venv, tenv, args->head, level, label);
                Ty_ty actualTy = actual_ty(argExpTy.ty);
                Ty_ty formalActualTy = actual_ty(formals->head);
                // Ty_ty formalActualTy = (formals->head);
                if (actualTy != formalActualTy) {
                    EM_error(42, "para type mismatch");
                }
                last = Tr_ExpListAppend(last, Tr_ExpList(argExpTy.exp, NULL));
                args = args->tail;
                formals = formals->tail;
            }
            if (args != NULL) {
                EM_error(a->pos, "too many params in function %s",
                         funcName->name);
            }
            Tr_exp tr =
                Tr_callExp(funcEntry->u.fun.label, Tr_ExpListTail(list));
            return expTy(tr, funcEntry->u.fun.result);
        }
        case A_opExp: {
            A_oper oper = a->u.op.oper;
            struct expty left =
                transExp(venv, tenv, a->u.op.left, level, label);
            struct expty right =
                transExp(venv, tenv, a->u.op.right, level, label);
            switch (oper) {
                case A_plusOp:
                case A_minusOp:
                case A_timesOp:
                case A_divideOp:
                    if (left.ty->kind != Ty_int)
                        EM_error(a->u.op.left->pos, "integer required");
                    if (right.ty->kind != Ty_int)
                        EM_error(a->u.op.right->pos, "integer required");
                    return expTy(Tr_opExp(oper, left.exp, right.exp), Ty_Int());
                case A_leOp:
                case A_geOp:
                case A_ltOp:
                case A_gtOp:
                    if (left.ty->kind != right.ty->kind)
                        EM_error(a->pos, "same type required");
                    return expTy(Tr_opExp(oper, left.exp, right.exp), Ty_Int());
                case A_eqOp:
                    return expTy(Tr_opExp(oper, left.exp, right.exp), Ty_Int());
                case A_neqOp:
                    if (left.ty->kind != right.ty->kind)
                        EM_error(a->pos, "same type required");
                    return expTy(NULL, Ty_Int());
                default:
                    printf("Unknown op\n");
                    break;
            }
            break;
        }
        case A_recordExp: {
            // TODO: record body type checking
            S_symbol symbol = a->u.record.typ;
            Ty_ty ty = S_look(tenv, symbol);
            if (ty == NULL) {
                EM_error(a->pos, "undefined type %s", symbol->name);
                return expTy(NULL, Ty_Nil());
            }
            A_efieldList fields = a->u.record.fields;
            A_efieldList cur = fields;
            Tr_expList list = Tr_ExpList(NULL, NULL);
            Tr_expList last = list;
            while (cur) {
                A_efield field = cur->head;
                struct expty val =
                    transExp(venv, tenv, field->exp, level, label);
                Tr_exp exp = val.exp;
                // TODO: record init
                last = Tr_ExpListAppend(last, Tr_ExpList(exp, NULL));
                cur = cur->tail;
            }
            list = Tr_ExpListTail(list);
            Tr_exp recTr = Tr_RecordExp(list);
            return expTy(recTr, ty);
        }
        case A_seqExp: {
            A_expList expList = a->u.seq;
            if (expList == NULL) return expTy(Tr_noOp(), Ty_Void());
            A_expList iter = expList;
            // return nil when seqExp is empty
            Ty_ty ty = Ty_Nil();
            struct expty transExpTy =
                transExp(venv, tenv, iter->head, level, label);
            Tr_exp trExp = transExpTy.exp;
            ty = transExpTy.ty;
            iter = iter->tail;
            while (iter) {
                A_exp exp = iter->head;
                transExpTy = transExp(venv, tenv, exp, level, label);
                ty = transExpTy.ty;
                trExp = Tr_SeqExp(trExp, transExpTy.exp);
                iter = iter->tail;
            }
            return expTy(trExp, ty);
        }
        case A_assignExp: {
            struct expty var =
                transVar(venv, tenv, a->u.assign.var, level, label);
            struct expty exp =
                transExp(venv, tenv, a->u.assign.exp, level, label);
            if (var.ty->kind != exp.ty->kind) {
                EM_error(a->pos, "unmatched assign exp");
            }
            return expTy(Tr_assignExp(var.exp, exp.exp), Ty_Void());
        }
        case A_ifExp: {
            struct expty testExp =
                transExp(venv, tenv, a->u.iff.test, level, label);
            struct expty thenExp =
                transExp(venv, tenv, a->u.iff.then, level, label);
            struct expty elseExp =
                transExp(venv, tenv, a->u.iff.elsee, level, label);
            int ifThenExp = elseExp.ty->kind == Ty_nil;
            Tr_exp trexp;
            if (ifThenExp) {
                // Note: <special case> in merge.tig
                // An expression is if xxx then xxx else nil, it's a
                // if-then-else expr but we can not distinguish it from if-then
                // expr
                if (thenExp.ty->kind != Ty_void &&
                    actual_ty(thenExp.ty)->kind != Ty_record)
                    EM_error(a->u.iff.then->pos,
                             "if-then exp's body must produce no value");
                trexp = Tr_ifThenExp(testExp.exp, thenExp.exp);
            } else {
                if (actual_ty(thenExp.ty) != actual_ty(elseExp.ty))
                    EM_error(a->u.iff.then->pos,
                             "then exp and else exp type mismatch");
                trexp = Tr_ifThenElseExp(testExp.exp, thenExp.exp, elseExp.exp);
                return expTy(trexp, thenExp.ty);
            }
            return expTy(trexp, Ty_Void());
        }
        case A_whileExp: {
            Temp_label done = Temp_newlabel();
            struct expty testExp =
                transExp(venv, tenv, a->u.whilee.test, level, label);
            struct expty bodyExp =
                transExp(venv, tenv, a->u.whilee.body, level, done);
            if (bodyExp.ty->kind != Ty_void)
                EM_error(a->u.whilee.body->pos,
                         "while body must produce no value");
            return expTy(Tr_whileExp(testExp.exp, bodyExp.exp, done),
                         Ty_Void());
        }
        case A_forExp: {
            S_symbol loopVar = a->u.forr.var;
            Tr_access acc = Tr_allocLocal(level, a->u.forr.escape);
            S_enter(venv, loopVar, E_VarEntry(acc, Ty_Int()));
            S_beginScope(venv);
            S_beginScope(tenv);
            Temp_label done = Temp_newlabel();  // label for break to jump to
            struct expty loExpr =
                transExp(venv, tenv, a->u.forr.lo, level, label);
            struct expty hiExpr =
                transExp(venv, tenv, a->u.forr.hi, level, label);
            struct expty body =
                transExp(venv, tenv, a->u.forr.body, level, done);
            if (loExpr.ty->kind != Ty_int)
                EM_error(a->u.forr.lo->pos,
                         "for exp's range type is not integer");
            if (hiExpr.ty->kind != Ty_int)
                EM_error(a->u.forr.hi->pos,
                         "for exp's range type is not integer");
            // No assign exp to index
            A_exp bodyExp = a->u.forr.body;
            switch (bodyExp->kind) {
                case A_seqExp: {
                    A_expList iter = bodyExp->u.seq;
                    while (iter) {
                        A_exp exp = iter->head;
                        if (exp->kind == A_assignExp &&
                            exp->u.assign.var->kind == A_simpleVar &&
                            exp->u.assign.var->u.simple == loopVar)
                            EM_error(exp->u.assign.var->pos,
                                     "loop variable can't be assigned");
                        iter = iter->tail;
                    }
                    break;
                }
                case A_assignExp: {
                    A_var assignVar = bodyExp->u.assign.var;
                    if (assignVar->kind == A_simpleVar &&
                        assignVar->u.simple == loopVar)
                        EM_error(bodyExp->u.assign.var->pos,
                                 "loop variable can't be assigned");
                }
                default:
                    break;
            }
            S_endScope(tenv);
            S_endScope(venv);
            return expTy(
                Tr_forExp(acc, level, loExpr.exp, hiExpr.exp, body.exp, done),
                Ty_Void());
        }
        case A_letExp: {
            struct expty exp;
            A_decList d;
            S_beginScope(venv);
            S_beginScope(tenv);
            d = a->u.let.decs;
            Tr_expList exps = NULL;
            Tr_expList tail = NULL;
            for (; d; d = d->tail) {
                Tr_exp exp = transDec(venv, tenv, d->head, level, label);
                if (exps == NULL) {
                    exps = tail = Tr_ExpList(exp, NULL);
                } else {
                    tail->tail = Tr_ExpList(exp, NULL);
                    tail = tail->tail;
                }
            }
            exp = transExp(venv, tenv, a->u.let.body, level, label);
            tail->tail = Tr_ExpList(exp.exp, NULL);
            S_endScope(tenv);
            S_endScope(venv);
            struct expty letExp;
            letExp.exp = Tr_listToExp(exps);
            letExp.ty = exp.ty;
            return letExp;
        }
        case A_arrayExp: {
            // The array initialization expression
            S_symbol sym = a->u.array.typ;
            Ty_ty ty = S_look(tenv, sym);
            A_exp size = a->u.array.size;
            A_exp init = a->u.array.init;
            Tr_exp tr;
            if (init) {
                struct expty sizeExpTy =
                    transExp(venv, tenv, size, level, label);
                struct expty initExpTy =
                    transExp(venv, tenv, init, level, label);
                if (actual_ty(initExpTy.ty) !=
                    actual_ty(actual_ty(ty)->u.array))
                    EM_error(a->pos, "type mismatch");
                tr = Tr_arrayExp(sizeExpTy.exp, initExpTy.exp);
            }
            return expTy(tr, ty);
        }
        case A_breakExp: {
            if (!label) {
                return expTy(Tr_noOp(), Ty_Void());
            }
            return expTy(Tr_breakExp(label), Ty_Void());
        }
        default:
            break;
    }
    printf("Unknown expr @%d kind %d\n", a->pos, a->kind);
    assert(0);
}

Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level level,
                Temp_label label) {
    switch (d->kind) {
        case A_varDec: {
            struct expty e = transExp(venv, tenv, d->u.var.init, level, label);
            S_symbol tySym = d->u.var.typ;
            if (tySym) {
                Ty_ty ty = S_look(tenv, tySym);
                Ty_ty initActualTy = actual_ty(e.ty);
                Ty_ty varActualTy = actual_ty(ty);
                if (initActualTy->kind == Ty_array &&
                    varActualTy->kind == Ty_array) {
                    if (actual_ty(initActualTy->u.array) !=
                        actual_ty(varActualTy->u.array))
                        EM_error(d->pos, "type mismatch");
                } else if (e.ty != ty && !(varActualTy->kind == Ty_record &&
                                           initActualTy->kind == Ty_nil))
                    EM_error(d->pos, "type mismatch");
            }
            if (e.ty->kind == Ty_nil && tySym == NULL)
                EM_error(d->pos,
                         "init should not be nil without type specified");
            Tr_access access = Tr_allocLocal(level, d->u.var.escape);
            S_enter(venv, d->u.var.var, E_VarEntry(access, e.ty));
            return Tr_varDec(access, e.exp);
        }
        case A_typeDec: {
            // dec: tydecs
            // First pass: put header (type xxx =) into env
            A_nametyList cur = d->u.type;
            while (cur) {
                S_symbol name = cur->head->name;
                if (cur->tail && name == cur->tail->head->name)
                    EM_error(d->pos, "two types have the same name");
                S_enter(tenv, name, Ty_Name(name, NULL));
                cur = cur->tail;
            }
            // Second pass: handle possible recursive types
            cur = d->u.type;
            while (cur) {
                Ty_ty named_ty = S_look(tenv, cur->head->name);
                Ty_ty ty = actual_ty(transTy(tenv, cur->head->ty));
                named_ty->u.name.ty = ty;
                if (ty->kind == Ty_name) {
                    EM_error(d->pos, "illegal type cycle");
                    break;
                }
                cur = cur->tail;
            };
            return Tr_noOp();
        }
        case A_functionDec: {
            A_fundecList cur = d->u.function;
            // First pass
            while (cur) {
                A_fundec f = cur->head;
                if (cur->tail && f->name == cur->tail->head->name)
                    EM_error(d->pos, "two functions have the same name");
                Ty_ty resultTy =
                    f->result ? S_look(tenv, f->result) : Ty_Void();
                Ty_tyList formalTys = makeFormalTyList(tenv, f->params);
                U_boolList boolList = makeBoolList(f->params);
                // use func name
                Temp_label newLevelLabel = Temp_namedlabel(S_name(f->name));
                Tr_level newLevel = Tr_newLevel(level, newLevelLabel, boolList);
                S_enter(
                    venv, f->name,
                    E_FunEntry(newLevel, newLevelLabel, formalTys, resultTy));
                cur = cur->tail;
            }
            // Second pass: processing the function body
            cur = d->u.function;
            while (cur) {
                A_fundec f = cur->head;
                Ty_tyList formalTys = makeFormalTyList(tenv, f->params);
                S_beginScope(venv);
                A_fieldList l = f->params;
                Ty_tyList t = formalTys;
                E_enventry funEntry = S_look(venv, f->name);
                Tr_level funcLevel = funEntry->u.fun.level;
                Tr_accessList accList = Tr_formals(funcLevel);
                for (; l; l = l->tail, t = t->tail, accList = accList->tail) {
                    // Tr_access acc = Tr_allocLocal(funcLevel,
                    // l->head->escape);
                    Tr_access acc = accList->head;
                    S_enter(venv, l->head->name, E_VarEntry(acc, t->head));
                }
                struct expty body =
                    transExp(venv, tenv, f->body, funcLevel, label);
                if (cur->head->result == NULL && body.ty->kind != Ty_void) {
                    EM_error(cur->head->pos, "procedure returns value");
                }
                S_endScope(venv);
                Tr_procEntryExit(funcLevel, body.exp, NULL);
                cur = cur->tail;
            }
            return Tr_noOp();
        }
    }
    assert(0);
}

/**
 * Translates type expressions as found in the abstract syntax (A_ty) to the
 * digested type descriptions that we will put into environments (Ty_ty);
 */
Ty_ty transTy(S_table tenv, A_ty a) {
    switch (a->kind) {
        case A_nameTy: {
            Ty_ty ty = S_look(tenv, a->u.name);
            return ty;
        }
        case A_recordTy: {
            A_fieldList list = a->u.record;
            Ty_fieldList tyFieldList = Ty_FieldList(
                Ty_Field(list->head->name, S_look(tenv, list->head->typ)),
                NULL);
            Ty_fieldList last = tyFieldList;
            list = list->tail;
            while (list) {
                A_field field = list->head;
                S_symbol name = field->name;
                Ty_ty ty = S_look(tenv, field->typ);
                if (ty == NULL) {
                    EM_error(field->pos, "undefined type %s", field->typ->name);
                    break;
                }
                Ty_field tyField = Ty_Field(name, ty);
                last = last->tail = Ty_FieldList(tyField, NULL);
                list = list->tail;
            }
            return Ty_Record(tyFieldList);
        }
        case A_arrayTy: {
            S_symbol sym = a->u.array;
            return Ty_Array(S_look(tenv, sym));
        }
    }
    assert(0);
}

F_fragList SEM_transProg(A_exp exp) {
    S_table venv = E_base_venv();
    S_table tenv = E_base_tenv();
    Tr_level mainLevel = Tr_newLevel(
        Tr_outermost(), Temp_namedlabel("tigermain"),  NULL);
    struct expty prog = transExp(venv, tenv, exp, mainLevel, NULL);
    Tr_procEntryExit(mainLevel, prog.exp, NULL);
    FILE* irOut = fopen("myir.dot", "w");
    printIR(irOut);
    fclose(irOut);
    return Tr_getResult();
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params) {
    A_fieldList cur = params;
    if (params == NULL) return NULL;
    Ty_tyList tyList = Ty_TyList(S_look(tenv, cur->head->typ), NULL);
    Ty_tyList last = tyList;
    cur = cur->tail;
    while (cur) {
        A_field field = cur->head;
        Ty_ty ty = S_look(tenv, field->typ);
        last = last->tail = Ty_TyList(ty, NULL);
        cur = cur->tail;
    }
    return tyList;
}

static U_boolList makeBoolList(A_fieldList params) {
    A_fieldList cur = params;
    if (params == NULL) return NULL;
    U_boolList boolList = U_BoolList(cur->head->escape, NULL);
    U_boolList last = boolList;
    cur = cur->tail;
    while (cur) {
        A_field field = cur->head;
        last = last->tail = U_BoolList(cur->head->escape, NULL);
        cur = cur->tail;
    }
    return boolList;
}
