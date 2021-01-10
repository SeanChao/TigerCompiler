#include <stdio.h>
#include <string.h>

#include "absyn.h"
#include "assem.h"
#include "color.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "tree.h"
#include "util.h"

#define INFINITE 100000

static Temp_tempList precolored;

static G_nodeList simplifyWorklist;
static G_nodeList freezeWorklist;  // low-degree move-related nodes
static G_nodeList spillWorklist;
static G_nodeList spilledNodes;
// registers that have been coalesced; when u <- v is coalesced, v is added to
// this set and u put back on some work-list
static G_nodeList coalescedNodes;
static G_nodeList coloredNodes;
static G_nodeList selectStack;

static Live_moveList worklistMoves;   // moves enabled for possible coalescing
static Live_moveList activeMoves;     // moves not yet ready for coalescing
static Live_moveList coalescedMoves;  // moves that has been coalesced
static Live_moveList constrainedMoves;
static Live_moveList frozenMoves;

// G_table adjSet;    // the set of interference edges (u, v) in the graph,
// reflexivity holds
// G_table adjList;   // adjacent list representation of the graph
G_table degree;    // G_node -> int (the degree of a node)
G_table moveList;  // G_node -> the list of moves it is associated with
G_table alias;
G_table color;  // G_node -> Temp_temp, map a node to a machine register
static G_table nodeCost;  // G_node -> cost of node, spill small first

static G_graph interferenceGraph;

#define K 16  // x86_64 machine register number

static void build();
/**
 * Allocate `initial` to proper worklist
 */
static void makeWorkList();
static void simplify();
static void coalesce();
static void selectSpill();
static void assignColors();
static void freeze();

static G_nodeList adjacent(G_node node);
static Live_moveList nodeMoves(G_node node);
static bool moveRelated(G_node node);
static void decrementDegree(G_node node);
static void enableMoves(G_nodeList nodes);

static G_node getAlias(G_node node);
static void addWorkList(G_node node);
static bool conservative(G_nodeList nodes);
static bool Ok(G_node l, G_node r);
static void freezeMoves(G_node nodes);
static void combine(G_node u, G_node v);

static bool allAdjacentOk(G_node v, G_node u);

static int getDegree(G_node node);
static void setDegree(G_node node, int deg);

static G_nodeList set(G_node node);
static Live_moveList moveSet(G_node src, G_node dst);
static Temp_temp getColor(G_node node);
static void setColor(G_node, Temp_temp);
static bool inPrecolored(G_node node);

static void nodeListPush(G_node n);
static G_node nodeListPop();

// defs

void build(Temp_tempList precolor, Live_moveList moves, G_graph ig,
           G_table nodeMove, G_table cost) {
    degree = G_empty();
    alias = G_empty();
    color = G_empty();
    moveList = nodeMove;

    simplifyWorklist = NULL;
    freezeWorklist = NULL;
    spillWorklist = NULL;
    spilledNodes = NULL;
    coalescedNodes = NULL;
    coloredNodes = NULL;
    selectStack = NULL;
    worklistMoves = moves;
    activeMoves = NULL;
    coalescedMoves = NULL;
    constrainedMoves = NULL;
    frozenMoves = NULL;

    nodeCost = cost;
    interferenceGraph = ig;

    precolored = precolor;
    G_nodeList nodes = G_nodes(ig);

    for (; nodes; nodes = nodes->tail) {
        G_node n = nodes->head;
        if (!inPrecolored(n))
            setDegree(n, G_degree(n) / 2);
        else
            setDegree(n, 233333);  // infinite degree
    }
}

static void simplify() {
    G_node node = simplifyWorklist->head;
    simplifyWorklist = simplifyWorklist->tail;
    nodeListPush(node);
    G_nodeList adj = adjacent(node);
    for (G_nodeList nl = adj; nl; nl = nl->tail) decrementDegree(nl->head);
}

static void coalesce() {
    Live_moveList m = worklistMoves;

    G_node x = getAlias(m->src);
    G_node y = getAlias(m->dst);
    G_node u = x, v = y;
    if (inPrecolored(y)) {
        u = y;
        v = x;
    }
    worklistMoves = moveListDiff(worklistMoves, m);
    if (u == v) {
        coalescedMoves = moveListUnion(coalescedMoves, m);
        addWorkList(u);
    } else if (inPrecolored(v) || G_goesTo(u, v)) {
        constrainedMoves = moveListUnion(constrainedMoves, m);
        addWorkList(u);
        addWorkList(v);
    } else if ((inPrecolored(u) && allAdjacentOk(v, u)) ||
               (!inPrecolored(u) &&
                conservative(nodeListUnion(adjacent(u), adjacent(v))))) {
        coalescedMoves = moveListUnion(coalescedMoves, m);
        combine(u, v);
        addWorkList(u);
    } else
        activeMoves = moveListUnion(activeMoves, m);
}

/**
 * forall t in adj(v) => Ok(t, u)
 */
static bool allAdjacentOk(G_node v, G_node u) {
    for (G_nodeList it = adjacent(v); it; it = it->tail) {
        if (!Ok(it->head, u)) return FALSE;
    }
    return TRUE;
}

static void makeWorkList() {
    G_nodeList nodes = G_nodes(interferenceGraph);
    for (; nodes; nodes = nodes->tail) {
        G_node n = nodes->head;
        if (inPrecolored(n)) continue;
        if (getDegree(n) >= K) {
            spillWorklist = nodeListUnion(spillWorklist, set(n));
        } else if (moveRelated(n)) {
            freezeWorklist = nodeListUnion(freezeWorklist, set(n));
        } else {
            simplifyWorklist = nodeListUnion(simplifyWorklist, set(n));
        }
    }
}

static G_nodeList adjacent(G_node node) {
    return nodeListDiff(G_succ(node),
                        nodeListUnion(selectStack, coalescedNodes));
}

static Live_moveList nodeMoves(G_node node) {
    // dumpAllMove();
    Live_moveList mov = G_look(moveList, node);
    return moveListJoin(mov, moveListUnion(activeMoves, worklistMoves));
}

static bool moveRelated(G_node node) { return nodeMoves(node) != NULL; }

static void decrementDegree(G_node node) {
    int d = getDegree(node);
    setDegree(node, d - 1);
    if (d == K && !inPrecolored(node)) {
        enableMoves(nodeListUnion(G_NodeList(node, NULL), adjacent(node)));
        spillWorklist = nodeListDiff(spillWorklist, set(node));
        if (moveRelated(node))
            freezeWorklist = nodeListUnion(freezeWorklist, set(node));
        else
            simplifyWorklist = nodeListUnion(simplifyWorklist, set(node));
    }
}

static void enableMoves(G_nodeList nodes) {
    for (G_nodeList it = nodes; it; it = it->tail) {
        G_node node = it->head;
        for (Live_moveList ml = nodeMoves(node); ml; ml = ml->tail) {
            if (moveListIn(activeMoves, ml)) {
                activeMoves =
                    moveListDiff(activeMoves, moveSet(ml->src, ml->dst));
                worklistMoves =
                    moveListUnion(worklistMoves, moveSet(ml->src, ml->dst));
            }
        }
    }
}

static void addWorkList(G_node node) {
    if (!inPrecolored(node) && !moveRelated(node) && getDegree(node) < K) {
        freezeWorklist = nodeListDiff(freezeWorklist, set(node));
        simplifyWorklist = nodeListUnion(simplifyWorklist, set(node));
    }
}

static bool conservative(G_nodeList nodes) {
    int k = 0;
    for (G_nodeList it = nodes; it; it = it->tail)
        if (getDegree(it->head) >= K) k++;
    return k < K;
}

static bool Ok(G_node l, G_node r) {
    return getDegree(l) < K || inPrecolored(l) || G_goesTo(l, r);
}

static G_node getAlias(G_node n) {
    return nodeListIn(coalescedNodes, n) ? getAlias(G_look(alias, n)) : n;
}

void addEdge(G_node u, G_node v) {
    if (!G_goesTo(u, v)) {
        G_addEdge(u, v);
        G_addEdge(v, u);
        setDegree(u, getDegree(u) + 1);
        setDegree(v, getDegree(v) + 1);
    }
}

static void combine(G_node u, G_node v) {
    // nodeInvariantCheck(G_nodes(interferenceGraph));
    if (nodeListIn(freezeWorklist, v))
        freezeWorklist = nodeListDiff(freezeWorklist, set(v));
    else
        spillWorklist = nodeListDiff(spillWorklist, set(v));
    coalescedNodes = nodeListUnion(coalescedNodes, set(v));
    G_enter(alias, v, u);
    // nodeInvariantCheck(G_nodes(interferenceGraph));
    //
    Live_moveList uml = G_look(moveList, u);
    Live_moveList vml = G_look(moveList, v);
    // nodeInvariantCheck(G_nodes(interferenceGraph));
    G_enter(moveList, u, moveListUnion(uml, vml));
    enableMoves(G_NodeList(v, NULL));
    // nodeInvariantCheck(G_nodes(interferenceGraph));
    G_nodeList nl = adjacent(v);
    for (; nl; nl = nl->tail) {
        G_node t = nl->head;
        addEdge(t, u);
        decrementDegree(t);
    }
    // nodeInvariantCheck(G_nodes(interferenceGraph));
    if (getDegree(u) >= K && G_inNodeList(u, freezeWorklist)) {
        freezeWorklist = nodeListDiff(freezeWorklist, set(u));
        spillWorklist = nodeListUnion(spillWorklist, set(u));
    }
    // nodeInvariantCheck(G_nodes(interfenceGraph));
}

static void freeze() {
    G_nodeList u = set(freezeWorklist->head);
    freezeWorklist = nodeListDiff(freezeWorklist, u);
    simplifyWorklist = nodeListUnion(simplifyWorklist, u);
    freezeMoves(u->head);
}

static void freezeMoves(G_node node) {
    Live_moveList nodes = nodeMoves(node);
    for (Live_moveList it = nodes; it; it = it->tail) {
        G_node x = it->src;
        G_node y = it->dst;
        G_node v = getAlias(y) == getAlias(node) ? getAlias(x) : getAlias(y);
        activeMoves = moveListDiff(activeMoves, it);
        frozenMoves = moveListUnion(frozenMoves, it);
        if (nodeMoves(v) == NULL && getDegree(v) < K) {
            freezeWorklist = nodeListDiff(freezeWorklist, set(v));
            simplifyWorklist = nodeListUnion(simplifyWorklist, set(v));
        }
    }
}

static void selectSpill() {
    G_node minCost = NULL;
    for (G_nodeList it = spillWorklist; it; it = it->tail) {
        G_node n = it->head;
        if (!minCost) minCost = it->head;
        if (getCost(nodeCost, n) < getCost(nodeCost, minCost)) minCost = n;
    }
    printf("spill %d: deg=%d\n", Temp_getnum(Live_gtemp(minCost)),
           getDegree(minCost));
    G_nodeList u = set(minCost);
    spillWorklist = nodeListDiff(spillWorklist, u);
    simplifyWorklist = nodeListUnion(simplifyWorklist, u);
    freezeMoves(u->head);
}

static void assignColors() {
    for (G_nodeList nl = G_nodes(interferenceGraph); nl; nl = nl->tail) {
        G_node n = nl->head;
        if (inPrecolored(n)) {
            setColor(n, Live_gtemp(n));
            coloredNodes = nodeListUnion(coloredNodes, set(n));
        }
    }
    while (selectStack) {
        G_node n = nodeListPop();
        if (nodeListIn(coloredNodes, (n))) continue;
        Temp_tempList okColors = precolored;
        G_nodeList adj = G_adj(n);
        for (; adj; adj = adj->tail) {
            G_node w = adj->head;
            if (nodeListIn(coloredNodes, getAlias(w)) ||
                inPrecolored(getAlias(w))) {
                okColors = Temp_tempListDiff(
                    okColors, Temp_TempList(getColor(getAlias(w)), NULL));
            }
        }
        if (!okColors) {
            spilledNodes = nodeListUnion(spilledNodes, set(n));
        } else {
            coloredNodes = nodeListUnion(coloredNodes, set(n));
            setColor(n, okColors->head);
        }
    }
    G_nodeList nl = coalescedNodes;
    for (; nl; nl = nl->tail) {
        G_node n = nl->head;
        setColor(n, getColor(getAlias(n)));
    }
}

struct COL_result COL_color(struct Live_graph liveGraph, Temp_map initial,
                            Temp_tempList regs) {
    G_graph ig = liveGraph.graph;
    Live_moveList moves = liveGraph.moves;
    G_table nodeToMove = liveGraph.nodeToMove;
    G_table nodeCost = liveGraph.nodeCost;
    struct COL_result ret;
    // moveListDump(stdout, moves);
    build(regs, moves, ig, nodeToMove, nodeCost);
    makeWorkList();

    do {
        if (simplifyWorklist != NULL)
            simplify();
        else if (worklistMoves != NULL)
            coalesce();
        else if (freezeWorklist != NULL)
            freeze();
        else if (spillWorklist != NULL)
            selectSpill();
    } while (!(simplifyWorklist == NULL && worklistMoves == NULL &&
               freezeWorklist == NULL && spillWorklist == NULL));
    assignColors();

    Temp_map tempMap = Temp_empty();
    for (G_nodeList nl = G_nodes(ig); nl; nl = nl->tail) {
        G_node n = nl->head;
        Temp_temp reg = getColor(n);
        if (reg) {
            Temp_enter(tempMap, Live_gtemp(n), Temp_look(initial, reg));
            printf("add mapping t%d => %s\n", Temp_getnum(Live_gtemp(n)),
                   Temp_look(initial, reg));
        }
    }
    ret.coloring = Temp_layerMap(tempMap, initial);

    Temp_tempList spillList = NULL;
    for (G_nodeList it = spilledNodes; it; it = it->tail)
        spillList = Temp_TempList(Live_gtemp(it->head), spillList);
    ret.spills = spillList;
    return ret;
}

static G_nodeList set(G_node node) { return G_NodeList(node, NULL); }

static Live_moveList moveSet(G_node src, G_node dst) {
    return Live_MoveList(src, dst, NULL);
}

static int getDegree(G_node node) { return *(int *)G_look(degree, node); }
static void setDegree(G_node node, int deg) {
    int *i = checked_malloc(sizeof(int));
    *i = deg;
    G_enter(degree, node, i);
}

static Temp_temp getColor(G_node node) { return G_look(color, node); }

static void setColor(G_node node, Temp_temp machineRegister) {
    G_enter(color, node, machineRegister);
}

static bool inPrecolored(G_node node) {
    return listLook(precolored, Live_gtemp(node));
}

static void nodeListPush(G_node n) {
    selectStack = nodeListUnion(selectStack, set(n));
}

static G_node nodeListPop() {
    G_node node = selectStack->head;
    selectStack = selectStack->tail;
    return node;
}

#ifdef INV_CHECK
#define

void G_nodelistDump(FILE *out, G_nodeList list) {
    for (G_nodeList iter = list; iter; iter = iter->tail) {
        fprintf(out, "t%d, ", Temp_getnum(G_nodeInfo(iter->head)));
    }
    fprintf(out, "\n");
};

static void dumpAllList() {
    fprintf(stdout, "list-precolored\t: ");
    Temp_dumpList(stdout, precolored);
    fprintf(stdout, "list-simplifyWorklist\t: ");
    G_nodelistDump(stdout, simplifyWorklist);
    fprintf(stdout, "list-freezeWorklist\t: ");
    G_nodelistDump(stdout, freezeWorklist);
    fprintf(stdout, "list-spillWorklist\t: ");
    G_nodelistDump(stdout, spillWorklist);
    fprintf(stdout, "list-spilledNodes\t: ");
    G_nodelistDump(stdout, spilledNodes);
    fprintf(stdout, "list-coalescedNodes\t: ");
    G_nodelistDump(stdout, coalescedNodes);
    fprintf(stdout, "list-coloredNodes\t: ");
    G_nodelistDump(stdout, coloredNodes);
    fprintf(stdout, "list-selectStack\t: ");
    G_nodelistDump(stdout, selectStack);
}

static void dumpAllMove() {
    fprintf(stdout, "move-worklistMoves\t: ");
    moveListDump(stdout, worklistMoves);
    fprintf(stdout, "move-activeMoves\t: ");
    moveListDump(stdout, activeMoves);
    fprintf(stdout, "move-coalescedMoves\t: ");
    moveListDump(stdout, coalescedMoves);
    fprintf(stdout, "move-constrainedMoves\t: ");
    moveListDump(stdout, constrainedMoves);
    fprintf(stdout, "move-frozenMoves\t: ");
    moveListDump(stdout, frozenMoves);
}


static void nodeInvariantCheck(G_nodeList nodes) {
    for (G_nodeList it = nodes; it; it = it->tail) {
        G_node n = it->head;
        // node is always in exactly ont of the sets or lists, these lists/sets
        // are mutually disjoint
        int count = inPrecolored(n) + nodeListIn(simplifyWorklist, n) +
                    nodeListIn(freezeWorklist, n) +
                    nodeListIn(spillWorklist, n) + nodeListIn(spilledNodes, n) +
                    nodeListIn(coalescedNodes, n) +
                    nodeListIn(coloredNodes, n) + nodeListIn(selectStack, n);
        if (count != 1) {
            fprintf(stderr,
                    "temp%d is not in a list or in more than one list: %d\n",
                    Temp_getnum(G_nodeInfo(n)), count);
            fprintf(stderr, "======debug\n");
            dumpAllList();
            dumpAllMove();
        }
        assert(count == 1);
    }
}
#endif
