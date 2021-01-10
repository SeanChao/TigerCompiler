/*
 * temp.c - functions to create and manipulate temporary variables which are
 *          used in the IR tree representation before it has been determined
 *          which variables are to go into registers.
 *
 */

#include "temp.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "symbol.h"
#include "table.h"
#include "util.h"

struct Temp_temp_ {
    int num;
};

int Temp_int(Temp_temp t) { return t->num; }

string Temp_labelstring(Temp_label s) { return S_name(s); }

static int labels = 0;

Temp_label Temp_newlabel(void) {
    char buf[100];
    sprintf(buf, "L%d", labels++);
    return Temp_namedlabel(String(buf));
}

/* The label will be created only if it is not found. */
Temp_label Temp_namedlabel(string s) { return S_Symbol(s); }

static int temps = 100;

Temp_temp Temp_newtemp(void) {
    Temp_temp p = (Temp_temp)checked_malloc(sizeof(*p));
    p->num = temps++;
    {
        char r[16];
        sprintf(r, "%d", p->num);
        Temp_enter(Temp_name(), p, String(r));
    }
    return p;
}

struct Temp_map_ {
    TAB_table tab;
    Temp_map under;
};

Temp_map Temp_name(void) {
    static Temp_map m = NULL;
    if (!m) m = Temp_empty();
    return m;
}

Temp_map Temp_newMap(TAB_table tab, Temp_map under) {
    Temp_map m = checked_malloc(sizeof(*m));
    m->tab = tab;
    m->under = under;
    return m;
}

Temp_map Temp_empty(void) { return Temp_newMap(TAB_empty(), NULL); }

Temp_map Temp_layerMap(Temp_map over, Temp_map under) {
    if (over == NULL)
        return under;
    else
        return Temp_newMap(over->tab, Temp_layerMap(over->under, under));
}

void Temp_enter(Temp_map m, Temp_temp t, string s) {
    assert(m && m->tab);
    TAB_enter(m->tab, t, s);
}

string Temp_look(Temp_map m, Temp_temp t) {
    string s;
    assert(m && m->tab);
    s = TAB_look(m->tab, t);
    if (s)
        return s;
    else if (m->under)
        return Temp_look(m->under, t);
    else
        return NULL;
}

Temp_tempList Temp_TempList(Temp_temp h, Temp_tempList t) {
    Temp_tempList p = (Temp_tempList)checked_malloc(sizeof(*p));
    p->head = h;
    p->tail = t;
    return p;
}

Temp_labelList Temp_LabelList(Temp_label h, Temp_labelList t) {
    Temp_labelList p = (Temp_labelList)checked_malloc(sizeof(*p));
    p->head = h;
    p->tail = t;
    return p;
}

static FILE *outfile;
void showit(Temp_temp t, string r) {
    fprintf(outfile, "t%d -> %s\n", t->num, r);
}

void Temp_dumpMap(FILE *out, Temp_map m) {
    outfile = out;
    TAB_dump(m->tab, (void (*)(void *, void *))showit);
    if (m->under) {
        fprintf(out, "---------\n");
        Temp_dumpMap(out, m->under);
    }
}

bool listLook(Temp_tempList list, Temp_temp t) {
    for (Temp_tempList iter = list; iter; iter = iter->tail) {
        if (iter->head == t) return TRUE;
    }
    return FALSE;
}

Temp_tempList Temp_tempListUnion(Temp_tempList lhs, Temp_tempList rhs) {
    // Temp_dumpList(stderr, lhs);
    // Temp_dumpList(stderr, rhs);
    Temp_tempList ret = rhs;
    for (Temp_tempList it = lhs; it; it = it->tail) {
        Temp_temp lt = it->head;
        // remove NULL
        if (lt == NULL) continue;
        Temp_tempList rIt;
        for (rIt = rhs; rIt; rIt = rIt->tail) {
            if (lt == rIt->head) break;
        }
        if (rIt == NULL) ret = Temp_TempList(lt, ret);
    }
    return ret;
}

Temp_tempList Temp_tempListDiff(Temp_tempList lhs, Temp_tempList rhs) {
    Temp_tempList ret = NULL;
    for (Temp_tempList lIt = lhs; lIt; lIt = lIt->tail) {
        Temp_temp nl = lIt->head;
        Temp_tempList rIt = NULL;
        for (rIt = rhs; rIt; rIt = rIt->tail) {
            Temp_temp nr = rIt->head;
            if (nl == nr) break;
        }
        if (rIt == NULL) ret = Temp_TempList(nl, ret);
    }
    return ret;
}

void Temp_append(Temp_tempList list, Temp_temp t) {
    Temp_tempList iter;
    for (iter = list; iter->tail; iter = iter->tail)
        ;
    iter->tail = Temp_TempList(t, NULL);
}

void Temp_dumpList(FILE *out, Temp_tempList list) {
    for (Temp_tempList iter = list; iter; iter = iter->tail) {
        fprintf(out, "temp%d, ", iter->head->num);
    }
    fprintf(out, "\n");
}

int Temp_getnum(Temp_temp t) { return t->num; }

void Temp_tempReplace(Temp_tempList l, Temp_temp origin, Temp_temp newTemp) {
    for (; l; l = l->tail) {
        if (l->head == origin) {
            l->head = newTemp;
        }
    }
}

void printLg(void *t) {
    t = (Temp_temp)t;
    printf("%d \n", Temp_getnum(t));
}
