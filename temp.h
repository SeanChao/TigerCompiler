/*
 * temp.h
 *
 */

#ifndef TEMP_H
#define TEMP_H

#include <stdio.h>
#include "symbol.h"
#include "table.h"

typedef struct Temp_temp_ *Temp_temp;
Temp_temp Temp_newtemp(void);
int Temp_int(Temp_temp);

typedef struct Temp_tempList_ *Temp_tempList;
struct Temp_tempList_ {
    Temp_temp head;
    Temp_tempList tail;
};
Temp_tempList Temp_TempList(Temp_temp h, Temp_tempList t);

typedef S_symbol Temp_label;
Temp_label Temp_newlabel(void);
Temp_label Temp_namedlabel(string name);
string Temp_labelstring(Temp_label s);

typedef struct Temp_labelList_ *Temp_labelList;
struct Temp_labelList_ {
    Temp_label head;
    Temp_labelList tail;
};
Temp_labelList Temp_LabelList(Temp_label h, Temp_labelList t);

typedef struct Temp_map_ *Temp_map;
Temp_map Temp_empty(void);
Temp_map Temp_layerMap(Temp_map over, Temp_map under);
void Temp_enter(Temp_map m, Temp_temp t, string s);
string Temp_look(Temp_map m, Temp_temp t);
void Temp_dumpMap(FILE *out, Temp_map m);
Temp_map Temp_newMap(TAB_table tab, Temp_map under);

Temp_map Temp_name(void);

bool listLook(Temp_tempList list, Temp_temp t);
Temp_tempList Temp_tempListUnion(Temp_tempList lhs, Temp_tempList rhs);
Temp_tempList Temp_tempListDiff(Temp_tempList lhs, Temp_tempList rhs);
void Temp_append(Temp_tempList list, Temp_temp t);
void Temp_dumpList(FILE *out, Temp_tempList list);

int Temp_getnum(Temp_temp t);

void Temp_tempReplace(Temp_tempList l, Temp_temp old, Temp_temp newTemp);

void printLg(void *t);
#endif
