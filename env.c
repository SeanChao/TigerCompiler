#include <stdio.h>

#include "util.h"

#include "symbol.h"

#include "env.h"

/*Lab4: Your implementation of lab4*/

E_enventry E_VarEntry(Ty_ty ty) {
    E_enventry ent = checked_malloc(sizeof(*ent));
    ent->kind = E_varEntry;
    ent->u.var.ty = ty;
    return ent;
}

E_enventry E_FunEntry(Ty_tyList formals, Ty_ty result) {
    E_enventry ent = checked_malloc(sizeof(*ent));
    ent->kind = E_funEntry;
    ent->u.fun.formals = formals;
    ent->u.fun.result = result;
    return ent;
}

S_table E_base_tenv(void) {
    S_table table = S_empty();
    S_enter(table, S_Symbol("int"), Ty_Int());
    S_enter(table, S_Symbol("string"), Ty_String());
    return table;
}

S_table E_base_venv(void) {
    S_table table = S_empty();
    S_enter(table, S_Symbol("print"),
            E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Void()));
    S_enter(table, S_Symbol("getchar"),
            E_FunEntry(Ty_TyList(NULL, NULL), Ty_String()));
    S_enter(table, S_Symbol("ord"),
            E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Int()));
    S_enter(table, S_Symbol("chr"),
            E_FunEntry(Ty_TyList(Ty_Int(), NULL), Ty_String()));
    return table;
}
