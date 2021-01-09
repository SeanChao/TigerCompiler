#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "absyn.h"
#include "assem.h"
#include "errormsg.h"
#include "flowgraph.h"
#include "frame.h"
#include "graph.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "tree.h"
#include "util.h"

AS_instr getInfo(G_node n) { return G_nodeInfo(n); }

Temp_tempList FG_def(G_node n) {
    AS_instr instr = getInfo(n);
    switch (instr->kind) {
        case I_OPER:
            return instr->u.OPER.dst;
        case I_MOVE:
            return instr->u.MOVE.dst;
        default:
            break;
    }
    return NULL;
}

Temp_tempList FG_use(G_node n) {
    AS_instr instr = getInfo(n);
    switch (instr->kind) {
        case I_OPER:
            return instr->u.OPER.src;
        case I_MOVE:
            return instr->u.MOVE.src;
        default:
            break;
    }
    return NULL;
}

bool FG_isMove(G_node n) { return getInfo(n)->kind == I_MOVE; }

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
    G_graph g = G_Graph();
    TAB_table labelNodeMap = TAB_empty();
    // create nodes for every instruction
    G_node last = NULL;
    for (AS_instrList iter = il; iter; iter = iter->tail) {
        // AS_print(stdout, iter->head, Temp_layerMap(F_tempMap, Temp_name()));
        G_node node = G_Node(g, iter->head);
        // if jmp, no sequential flow
        if (iter->head->kind == I_OPER && iter->head->u.OPER.jumps != NULL) {
            if (last != NULL) G_addEdge(last, node);
            last = NULL;
        } else {
            if (last != NULL) G_addEdge(last, node);
            last = node;
        }
        // label -> node: for jump flow construction
        if (iter->head->kind == I_LABEL)
            TAB_enter(labelNodeMap, iter->head->u.LABEL.label, node);
    }
    // add jump related edges
    for (G_nodeList nodeIter = G_nodes(g); nodeIter;
         nodeIter = nodeIter->tail) {
        G_node node = nodeIter->head;
        AS_instr instr = G_nodeInfo(node);
        // AS_print(stdout, instr, Temp_layerMap(F_tempMap, Temp_name()));
        if (instr->kind == I_OPER) {
            AS_targets jmpTargets = instr->u.OPER.jumps;
            if (jmpTargets == NULL) continue;
            Temp_labelList list = jmpTargets->labels;
            for (Temp_labelList iter = list; iter; iter = iter->tail) {
                G_addEdge(node, TAB_look(labelNodeMap, iter->head));
            }
        }
    }
    return g;
}
