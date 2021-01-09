#ifndef LIVENESS_H
#define LIVENESS_H

#include "graph.h"
#include "temp.h"

typedef struct Live_moveList_ *Live_moveList;
struct Live_moveList_ {
    G_node src, dst;
    Live_moveList tail;
};

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail);

/**
 * graph: an interference graph
 *
 * moves: a list of node-pairs (representing MOVE instructions) that should be
 * assigned the same register if possible
 */
struct Live_graph {
    G_graph graph;
    Live_moveList moves;
    G_table nodeToMove;
    G_table nodeCost;
};

/**
 * Live_gtemp tells what temporary variable is represented by n
 */
Temp_temp Live_gtemp(G_node n);

struct Live_graph Live_liveness(G_graph flow);

bool moveListIn(Live_moveList list, Live_moveList move);
Live_moveList moveListUnion(Live_moveList list, Live_moveList node);
Live_moveList moveListJoin(Live_moveList lhs, Live_moveList rhs);
Live_moveList moveListDiff(Live_moveList lhs, Live_moveList rhs);

void moveListDump(FILE *out, Live_moveList list);

double getCost(G_table t, G_node node);
#endif
