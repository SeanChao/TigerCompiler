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

// decs

static Temp_tempList precolored;
static G_nodeList precoloredNodes;  // the same as precolored, but node
// temporary registers, not precolored and not yet processed
static G_nodeList initial;
static G_nodeList simplifyWorklist;
static G_nodeList freezeWorklist;  // low-degree move-related nodes
static G_nodeList spillWorklist;
static G_nodeList spilledNodes;
// registers that have been coalesced; when u <- v is coalesced, v is added to
// this set and u put back on some work-list
static G_nodeList coalescedNodes;
static G_nodeList coloredNodes;
// stack containing temporaries removed from the graph
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

G_graph interfenceGraph;

// static const int K = 16;
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
static G_nodeList getAdjacent(G_node node);
static bool inPrecolored(G_node node);

static void dumpAllMove();

static void nodeInvariantCheck(G_nodeList nodes);
void G_nodelistDump(FILE *out, G_nodeList list);
// defs

static void graphCheck() {
    G_graph ig = interfenceGraph;
    for (G_nodeList nodes = G_nodes(ig); nodes; nodes = nodes->tail) {
        G_node node = nodes->head;
        int deg = 0;
        for (G_nodeList it = adjacent(node); it; it = it->tail) {
            deg++;
        }
        // int refDeg = G_look(degree, node);
        int refDeg = getDegree(node);
        assert(deg == refDeg);
    }
}

/**
 * Initialize
 */
static void build(Temp_tempList precolor, Live_moveList moves, G_graph ig,
                  G_table nodeMove) {
    interfenceGraph = ig;
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

    precolored = precolor;
    G_nodeList nodes = G_nodes(ig);
    precoloredNodes = NULL;
    for (G_nodeList it = nodes; it; it = it->tail) {
        G_node n = it->head;
        if (listLook(precolor, G_nodeInfo(n))) {
            precoloredNodes = G_NodeList(n, precoloredNodes);
        }
    }
    initial = NULL;
    // FIXME:
    for (G_nodeList it = nodes; it; it = it->tail) {
        G_node n = it->head;
        if (!inPrecolored(n)) {
            initial = G_NodeList(n, initial);
            // G_enter(degree, n, G_degree(n) / 2);
            setDegree(n, G_degree(n) / 2);
        } else {
            // G_enter(degree, n, G_degree(n) / 2);
            setDegree(n, G_degree(n) / 2);
        }
    }
    // assign colors for precolored nodes
    for (G_nodeList it = nodes; it; it = it->tail) {
        G_node n = it->head;
        if (inPrecolored(n)) {
            setColor(n, Live_gtemp(n));  // t100 -> t100, etc
            // coloredNodes = nodeListUnion(coloredNodes, set(n));
        }
    }
}

static void simplify() {
    G_node node = simplifyWorklist->head;
    simplifyWorklist = simplifyWorklist->tail;
    selectStack = push(selectStack, node);
    G_nodeList adj = adjacent(node);
    for (G_nodeList nl = adj; nl; nl = nl->tail) decrementDegree(nl->head);
}

static void coalesce() {
    // coalesce one pair
    Live_moveList m =
        Live_MoveList(worklistMoves->src, worklistMoves->dst, NULL);
    G_node x = getAlias(worklistMoves->src);
    G_node y = getAlias(worklistMoves->dst);
    G_node u = x, v = y;
    if (inPrecolored(y)) {
        u = y;
        v = x;
    }
    worklistMoves = worklistMoves->tail;
    // nodeInvariantCheck(G_nodes(interfenceGraph));
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
    for (G_nodeList it = getAdjacent(v); it; it = it->tail) {
        if (!Ok(it->head, u)) return FALSE;
    }
    return TRUE;
}

static void makeWorkList() {
    for (G_nodeList it = initial; it; it = it->tail) {
        G_node node = it->head;
        int deg = getDegree(node);
        if (deg >= K) {
            spillWorklist = nodeListUnion(spillWorklist, set(node));
        } else if (moveRelated(node)) {
            freezeWorklist = nodeListUnion(freezeWorklist, set(node));
        } else
            simplifyWorklist = nodeListUnion(simplifyWorklist, set(node));
    }
    printf("simp: ");
    G_nodelistDump(stdout, simplifyWorklist);
    printf("freeze: ");
    G_nodelistDump(stdout, freezeWorklist);
    initial = NULL;
}

static G_nodeList adjacent(G_node node) {
    return nodeListDiff(G_succ(node),
                        nodeListUnion(selectStack, coalescedNodes));
}

static Live_moveList nodeMoves(G_node node) {
    // dumpAllMove();
    Live_moveList mov = G_look(moveList, node);
    // moves from this node to other nodes
    // for (G_nodeList nl = G_nodes(interfenceGraph); nl; nl = nl->tail) {
    //     G_node n = nl->head;
    //     if (n == node) continue;
    //     int t = Temp_getnum(Live_gtemp(n));
    //     Live_moveList ml = G_look(moveList, n);
    //     // if (!ml) continue;
    //     while (ml) {
    //         if (ml->dst == node)
    //             mov = moveListUnion(mov, moveSet(ml->src, ml->dst));
    //         ml = ml->tail;
    //     }
    // }
    // fprintf(stdout, "mov: ");
    // moveListDump(stdout, mov);
    return moveListJoin(mov, moveListUnion(activeMoves, worklistMoves));
}

static bool moveRelated(G_node node) { return nodeMoves(node) != NULL; }

static void decrementDegree(G_node node) {
    int d = getDegree(node) - 1;
    setDegree(node, d);
    if (d == K && !inPrecolored(node)) {
        enableMoves(nodeListUnion(G_NodeList(node, NULL), getAdjacent(node)));
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
    for (G_nodeList it = 0; it; it = it->tail)
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
        // G_enter(degree, u, getDegree(u) + 1);
        // G_enter(degree, v, getDegree(v) + 1);
        setDegree(u, getDegree(u) + 1);
        setDegree(v, getDegree(v) + 1);
    }
}

static void combine(G_node u, G_node v) {
    nodeInvariantCheck(G_nodes(interfenceGraph));
    if (nodeListIn(freezeWorklist, v))
        freezeWorklist = nodeListDiff(freezeWorklist, set(v));
    else
        spillWorklist = nodeListDiff(spillWorklist, set(v));
    coalescedNodes = nodeListUnion(coalescedNodes, set(v));
    G_enter(alias, v, u);
    nodeInvariantCheck(G_nodes(interfenceGraph));
    //
    Live_moveList uml = G_look(moveList, u);
    Live_moveList vml = G_look(moveList, v);
    nodeInvariantCheck(G_nodes(interfenceGraph));
    G_enter(moveList, u, moveListUnion(uml, vml));
    enableMoves(G_NodeList(v, NULL));
    nodeInvariantCheck(G_nodes(interfenceGraph));
    G_nodeList nl = adjacent(v);
    for (; nl; nl = nl->tail) {
        G_node t = nl->head;
        addEdge(t, u);
        decrementDegree(t);
    }
    nodeInvariantCheck(G_nodes(interfenceGraph));
    if (getDegree(u) >= K && G_inNodeList(u, freezeWorklist)) {
        freezeWorklist = nodeListDiff(freezeWorklist, set(u));
        spillWorklist = nodeListUnion(spillWorklist, set(u));
    }
    // nodeInvariantCheck(G_nodes(interfenceGraph));
}

static void freeze() {
    for (G_nodeList it = freezeWorklist; it; it = it->tail) {
        G_nodeList u = set(it->head);
        freezeWorklist = nodeListDiff(freezeWorklist, u);
        simplifyWorklist = nodeListUnion(simplifyWorklist, u);
        freezeMoves(u->head);
    }
}

/**
 */
static void freezeMoves(G_node node) {
    Live_moveList nodes = nodeMoves(node);
    for (Live_moveList it = nodes; it; it = it->tail) {
        G_node x = it->src;
        G_node y = it->dst;
        G_node v = getAlias(y) == getAlias(node) ? getAlias(x) : getAlias(node);
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
    while (selectStack && selectStack->head != NULL) {
        G_node n = nodePop(selectStack);
        Temp_tempList okColors = precolored;
        G_nodeList graphAdj = G_adj(n);
        printf("node %d's adjacent: \n", Temp_getnum(Live_gtemp(n)));
        G_nodelistDump(stdout, graphAdj);
        for (G_nodeList it = graphAdj; it; it = it->tail) {
            G_node w = it->head;
            G_node aliased = getAlias(w);
            if (nodeListIn(nodeListUnion(coloredNodes, precoloredNodes),
                           aliased))
                okColors = Temp_tempListDiff(
                    okColors, Temp_TempList(getColor(aliased), NULL));
            // printf("OK colors turn into:\n");
            // Temp_dumpList(stdout, okColors);
        }
        if (okColors == NULL) {
            spilledNodes = nodeListUnion(spilledNodes, set(n));
            printf("spill %d\n", Temp_getnum(Live_gtemp(n)));
        } else {
            coloredNodes = nodeListUnion(coloredNodes, set(n));
            printf("OK colors:\n");
            Temp_dumpList(stdout, okColors);
            setColor(n, (okColors->head));
            printf("color %d to %d\n", Temp_getnum(Live_gtemp(n)),
                   Temp_getnum((okColors->head)));
        }
    }

    for (G_nodeList it = coalescedNodes; it; it = it->tail) {
        G_node n = it->head;
        Temp_temp col = getColor(getAlias(n));
        setColor(n, col);
    }
}

void G_nodelistDump(FILE *out, G_nodeList list) {
    for (G_nodeList iter = list; iter; iter = iter->tail) {
        fprintf(out, "t%d, ", Temp_getnum(G_nodeInfo(iter->head)));
    }
    fprintf(out, "\n");
};

static void dumpAllList() {
    fprintf(stdout, "list-precolored\t: ");
    Temp_dumpList(stdout, precolored);
    fprintf(stdout, "list-initial\t: ");
    G_nodelistDump(stdout, initial);
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
    return;
    for (G_nodeList it = nodes; it; it = it->tail) {
        G_node n = it->head;
        // node is always in exactly ont of the sets or lists, these lists/sets
        // are mutually disjoint
        int count = inPrecolored(n) + nodeListIn(initial, n) +
                    nodeListIn(simplifyWorklist, n) +
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

static void invariantCheck() {
    // degree invariant
}

struct COL_result COL_color(struct Live_graph liveGraph, Temp_map initial,
                            Temp_tempList regs) {
    G_graph ig = liveGraph.graph;
    Live_moveList moves = liveGraph.moves;
    G_table nodeToMove = liveGraph.nodeToMove;
    nodeCost = liveGraph.nodeCost;

    struct COL_result ret;
    build(regs, moves, ig, nodeToMove);
    makeWorkList();
    nodeInvariantCheck(G_nodes(ig));
    int _niter = 0;
    do {
        _niter++;
        nodeInvariantCheck(G_nodes(ig));
        printf("======before====== iter-%d\n", _niter);
        dumpAllList();
        dumpAllMove();

        if (simplifyWorklist != NULL)
            simplify();
        else if (worklistMoves != NULL)
            coalesce();
        else if (freezeWorklist != NULL)
            freeze();
        else if (spillWorklist != NULL)
            selectSpill();
        nodeInvariantCheck(G_nodes(ig));
        for (G_nodeList it = G_nodes(ig); it; it = it->tail) {
            G_node n = it->head;
            printf("node %d's adjacent: \n\t", Temp_getnum(Live_gtemp(n)));
            G_nodelistDump(stdout, adjacent(n));
        }
        // graphCheck();
    } while (!(simplifyWorklist == NULL && worklistMoves == NULL &&
               freezeWorklist == NULL && spillWorklist == NULL));
    assignColors();
    // TAB_dump(get)
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
    for (G_nodeList it = spilledNodes; it; it = it->tail) {
        spillList = Temp_TempList(Live_gtemp(it->head), spillList);
    }
    ret.spills = spillList;
    return ret;
}

// static G_nodeList getAdjacent(G_node node) { return G_look(adjacent, node); }
static G_nodeList getAdjacent(G_node node) { return adjacent(node); }
// static G_nodeList getAdjList(G_node node) { return adjacent(node); }

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
