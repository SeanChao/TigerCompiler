#include "liveness.h"
#include <stdio.h>
#include "absyn.h"
#include "assem.h"
#include "flowgraph.h"
#include "frame.h"
#include "graph.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "tree.h"
#include "util.h"

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
    Live_moveList lm = (Live_moveList)checked_malloc(sizeof(*lm));
    lm->src = src;
    lm->dst = dst;
    lm->tail = tail;
    return lm;
}

Temp_temp Live_gtemp(G_node n) {
    // your code here.
    return NULL;
}

struct Live_graph Live_liveness(G_graph flow) {
    // your code here.
    struct Live_graph lg;
    return lg;
}
