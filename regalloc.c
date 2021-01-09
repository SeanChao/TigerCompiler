#include "regalloc.h"
#include <stdio.h>
#include "absyn.h"
#include "assem.h"
#include "color.h"
#include "flowgraph.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "tree.h"
#include "util.h"

void printLg(Temp_temp t) {
    printf("%d ", Temp_getnum(t));
    printf("\n");
}

static void printCfgInfo(AS_instr ins) {
    AS_print(stdout, ins, Temp_layerMap(F_tempMap, Temp_name()));
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
    struct RA_result ret;

    G_graph cfg = FG_AssemFlowGraph(il, f);
    G_show(stderr, G_nodes(cfg), printCfgInfo);
    struct Live_graph liveGraph = Live_liveness(cfg);
    G_show(stdout, G_nodes(liveGraph.graph), printLg);
    struct COL_result col = COL_color(liveGraph, F_tempMap, F_registers());
    if (col.spills != NULL) {
        il = AS_rewriteSpill(f, il, col.spills);
        printf("====rewrite====\n");
        AS_printInstrList(stdout, il, Temp_layerMap(F_tempMap, Temp_name()));
        return RA_regAlloc(f, il);
    }
    AS_instrList rewrite = AS_rewrite(il, col.coloring);
    ret.il = rewrite;
    ret.coloring = col.coloring;
    return ret;
}
