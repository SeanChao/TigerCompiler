#include "escape.h"
#include <stdio.h>
#include <string.h>
#include "absyn.h"
#include "symbol.h"
#include "table.h"
#include "util.h"

static void traverseExp(S_table env, int depth, A_exp root);
static void traverseDec(S_table env, int depth, A_dec root);
static void traverseVar(S_table env, int depth, A_var root);

struct _EscapeEntry {
    int depth;
    bool *escape;
};

typedef struct _EscapeEntry *EscapeEntry;

static EscapeEntry newEscapeEntry(int depth, bool *escape) {
    EscapeEntry ent = checked_malloc(sizeof(*ent));
    ent->depth = depth;
    ent->escape = escape;
    return ent;
}

void Esc_findEscape(A_exp exp) {
    /**
     * A variable "escapes" if it's address is taken or it's accessed from a
     * nested function For the tiger language, only the latter case is
     * considerred.
     */

    S_table env = S_empty();
    traverseExp(env, 0, exp);
}

static void traverseExp(S_table env, int depth, A_exp root) {
    A_exp e = root;
    switch (root->kind) {
        case A_varExp:
            traverseVar(env, depth, root->u.var);
            break;
        case A_callExp:
            for (A_expList arg = root->u.call.args; arg; arg = arg->tail) {
                traverseExp(env, depth, arg->head);
            }
            break;
        case A_opExp:
            traverseExp(env, depth, root->u.op.left);
            traverseExp(env, depth, root->u.op.right);
            break;
        case A_recordExp:
            for (A_efieldList fields = root->u.record.fields; fields;
                 fields = fields->tail) {
                traverseExp(env, depth, fields->head->exp);
            }
            break;
        case A_seqExp:
            for (A_expList cur = root->u.seq; cur; cur = cur->tail) {
                traverseExp(env, depth, cur->head);
            }
            break;
        case A_assignExp:
            traverseVar(env, depth, root->u.assign.var);
            traverseExp(env, depth, root->u.assign.exp);
            break;
        case A_ifExp:
            traverseExp(env, depth, root->u.iff.test);
            traverseExp(env, depth, root->u.iff.then);
            if (root->u.iff.elsee) traverseExp(env, depth, root->u.iff.elsee);
            break;
        case A_whileExp:
            traverseExp(env, depth, root->u.whilee.test);
            traverseExp(env, depth, root->u.whilee.body);
            break;
        case A_forExp:
            traverseExp(env, depth, e->u.forr.lo);
            traverseExp(env, depth, e->u.forr.hi);
            S_beginScope(env);
            e->u.forr.escape = FALSE;
            S_enter(env, e->u.forr.var,
                    newEscapeEntry(depth, &e->u.forr.escape));
            traverseExp(env, depth, e->u.forr.body);
            S_endScope(env);
            break;
        case A_letExp:
            S_beginScope(env);
            for (A_decList d = e->u.let.decs; d; d = d->tail) {
                traverseDec(env, depth, d->head);
            }
            traverseExp(env, depth, e->u.let.body);
            S_endScope(env);
            break;
        case A_arrayExp:
            traverseExp(env, depth, e->u.array.size);
            traverseExp(env, depth, e->u.array.init);
            break;
        case A_breakExp:
        case A_nilExp:
        case A_intExp:
        case A_stringExp:
            break;
        default:
            assert(0);
            break;
    }
}

static void traverseDec(S_table env, int depth, A_dec root) {
    A_dec d = root;
    switch (d->kind) {
        case A_functionDec:
            for (A_fundecList fun = d->u.function; fun; fun = fun->tail) {
                S_beginScope(env);
                for (A_fieldList l = fun->head->params; l; l = l->tail) {
                    l->head->escape = FALSE;
                    S_enter(env, l->head->name,
                            newEscapeEntry(depth + 1, &l->head->escape));
                }
                traverseExp(env, depth + 1, fun->head->body);
                S_endScope(env);
            }
            break;
        case A_varDec:
            traverseExp(env, depth, d->u.var.init);
            d->u.var.escape = FALSE;
            S_enter(env, d->u.var.var, newEscapeEntry(depth, &d->u.var.escape));
            break;
        case A_typeDec:
            break;
        default:
            assert(0);
            break;
    }
}

static void traverseVar(S_table env, int depth, A_var root) {
    A_var v = root;
    switch (v->kind) {
        case A_simpleVar: {
            EscapeEntry esc = S_look(env, v->u.simple);
            if (esc->depth < depth) {
                *(esc->escape) = TRUE;
            }
            break;
        }
        case A_fieldVar:
            traverseVar(env, depth, v->u.field.var);
            break;
        case A_subscriptVar:
            traverseVar(env, depth, v->u.subscript.var);
            traverseExp(env, depth, v->u.subscript.exp);
            break;
        default:
            assert(0);
            break;
    }
}
