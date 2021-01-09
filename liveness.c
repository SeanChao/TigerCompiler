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

// static Temp_tempList setSubstraction(Temp_tempList l, Temp_tempList r) {
//     // for each item in r, remove it if it's in l
//     for (Temp_tempList rIter = r; rIter; rIter = rIter->tail) {
//         for (Temp_tempList lIter = l; lIter; lIter = lIter->tail) {
//         }
//     }
// }
double getCost(G_table t, G_node node) {
    double *p = G_look(t, node);
    if (p) return *p;
    return 0.0;
}

static void setCost(G_table t, G_node node, double d) {
    double *p = G_look(t, node);
    if (!p) {
        p = checked_malloc(sizeof(double));
        G_enter(t, node, p);
    }
    *p = d;
}

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
    Live_moveList lm = (Live_moveList)checked_malloc(sizeof(*lm));
    lm->src = src;
    lm->dst = dst;
    lm->tail = tail;
    return lm;
}

Temp_temp Live_gtemp(G_node n) { return G_nodeInfo(n); }

static void printLg(Temp_temp t) {
    printf("%d ", Temp_getnum(t));
    printf("\n");
}

static void printCfgInfo(AS_instr ins) {
    AS_print(stdout, ins, Temp_layerMap(F_tempMap, Temp_name()));
}

struct Live_graph Live_liveness(G_graph flow) {
    struct Live_graph lg;
    // Liveness analysis
    G_table liveIn = G_empty();
    G_table liveOut = G_empty();
    bool nochange = FALSE;
    while (!nochange) {
        nochange = TRUE;
        // repeat for each node
        for (G_nodeList nl = G_nodes(flow); nl; nl = nl->tail) {
            G_node node = nl->head;
            Temp_tempList nodeIn = G_look(liveIn, node);
            Temp_tempList nodeOut = G_look(liveOut, node);
            // out <- union of all successors' in
            G_nodeList succ = G_succ(node);
            for (G_nodeList iter = succ; iter; iter = iter->tail) {
                G_node s = iter->head;
                Temp_tempList succIn = G_look(liveIn, s);
                for (Temp_tempList tIter = succIn; tIter; tIter = tIter->tail) {
                    if (tIter->head && !listLook(nodeOut, tIter->head)) {
                        nodeOut = Temp_TempList(tIter->head, nodeOut);
                        nochange = FALSE;
                    }
                }
            }
            // in <- use + (out - def)
            // add nodes in use
            Temp_tempList use = FG_use(node);
            for (Temp_tempList iter = use; iter; iter = iter->tail) {
                Temp_temp t = iter->head;
                if (t && !listLook(nodeIn, t)) {
                    nodeIn = Temp_tempListUnion(Temp_TempList(t, NULL), nodeIn);
                    nochange = FALSE;
                }
            }
            // add nodes in out but not in def
            Temp_tempList def = FG_def(node);
            for (Temp_tempList iter = nodeOut; iter; iter = iter->tail) {
                Temp_temp t = iter->head;
                if (t && !listLook(nodeIn, t) && !listLook(def, t)) {
                    nodeIn = Temp_tempListUnion(Temp_TempList(t, NULL), nodeIn);
                    nochange = FALSE;
                }
            }
            // fprintf(stderr, "nodeout:");
            // Temp_dumpList(stderr, nodeOut);
            G_enter(liveIn, node, nodeIn);
            G_enter(liveOut, node, nodeOut);

            // printf("==iter-liveness\n");
            // for (G_nodeList it = G_nodes(flow); it; it = it->tail) {
            //     G_node node = it->head;
            //     printCfgInfo(G_nodeInfo(node));
            //     if (FG_def(node) == NULL) continue;
            //     Temp_tempList tempOut = G_look(liveOut, node);
            //     Temp_tempList tempIn = G_look(liveIn, node);
            //     printf("[out]\t");
            //     Temp_dumpList(stdout, tempOut);
            //     printf("[in]\t");
            //     Temp_dumpList(stdout, tempIn);
            // }
        }
    }

    // construct interference graph
    // iterate through the graph and add edges <def, out>
    G_graph interference = G_Graph();
    // add all machine registers and virtual registers
    G_nodeList nodeList = G_nodes(flow);
    Temp_tempList merged = NULL;
    for (G_nodeList nlIter = nodeList; nlIter; nlIter = nlIter->tail) {
        G_node node = nlIter->head;
        Temp_tempList use = FG_use(node);
        Temp_tempList def = FG_def(node);
        Temp_tempList useAndDef = Temp_tempListUnion(use, def);
        merged = Temp_tempListUnion(merged, useAndDef);
        // Temp_dumpList(stderr, merged);
    }
    merged = Temp_tempListUnion(merged, F_registers());
    Temp_dumpList(stderr, merged);
    TAB_table interferenceMap = TAB_empty();  // map temp to node
    for (Temp_tempList it = merged; it; it = it->tail) {
        Temp_temp temp = it->head;
        G_node node = G_Node(interference, temp);
        TAB_enter(interferenceMap, temp, node);
    }
    // Add interference edges
    // add interference edges between all machine registers
    // TODO:
    for (G_nodeList iter = nodeList; iter; iter = iter->tail) {
        G_node node = iter->head;
        printCfgInfo(G_nodeInfo(node));
        Temp_tempList l = FG_def(node);
        if (l == NULL) continue;
        Temp_tempList r = G_look(liveOut, node);
        if (FG_isMove(node)) {
            r = Temp_tempListDiff(r, FG_use(node));
        }
        // Temp_dumpList(stdout, l);
        // printf("x ");
        // Temp_dumpList(stdout, r);
        for (Temp_tempList it1 = l; it1; it1 = it1->tail) {
            for (Temp_tempList it2 = r; it2; it2 = it2->tail) {
                G_node lNode = TAB_look(interferenceMap, it1->head);
                G_node rNode = TAB_look(interferenceMap, it2->head);
                if (lNode == rNode) continue;
                G_addEdge(lNode, rNode);
                G_addEdge(rNode, lNode);
                // printf("%d<->%d ", Temp_getnum(it1->head),
                //        Temp_getnum(it2->head));
            }
        }
    }
    // G_show(stdout, G_nodes(interference), printLg);
    // Build Movelist
    Live_moveList moveList = NULL;
    G_table nodeToMove = G_empty();
    for (G_nodeList iter = nodeList; iter; iter = iter->tail) {
        G_node node = iter->head;
        if (FG_isMove(node)) {
            AS_instr instr = G_nodeInfo(node);
            // FIXME: is from/to lists with one element?
            Temp_temp from = instr->u.MOVE.src->head;
            Temp_temp to = instr->u.MOVE.dst->head;
            if (!from) continue;  // src is not a register
            G_node srcNode = TAB_look(interferenceMap, from);
            G_node dstNode = TAB_look(interferenceMap, to);
            moveList = Live_MoveList(srcNode, dstNode, moveList);
            G_enter(
                nodeToMove, srcNode,
                Live_MoveList(srcNode, dstNode, G_look(nodeToMove, srcNode)));
        }
    }
    // Calculate cost for all temps
    G_table nodeCost = G_empty();
    for (G_nodeList it = G_nodes(flow); it; it = it->tail) {
        G_node node = it->head;
        Temp_tempList def = FG_def(node);
        Temp_tempList use = FG_use(node);
        for (Temp_tempList it = def; it; it = it->tail) {
            G_node tempNode = TAB_look(interferenceMap, it->head);
            setCost(nodeCost, tempNode, getCost(nodeCost, tempNode) + 1.0);
        }
        for (Temp_tempList it = use; it && it->head; it = it->tail) {
            G_node tempNode = TAB_look(interferenceMap, it->head);
            setCost(nodeCost, tempNode, getCost(nodeCost, tempNode) + 1.0);
        }
    }
    G_nodeList nl = G_nodes(interference);
    for (; nl; nl = nl->tail) {
        G_node n = nl->head;
        setCost(nodeCost, n, getCost(nodeCost, n) / (G_degree(n) / 2));
    }

    lg.graph = interference;
    lg.moves = moveList;
    lg.nodeToMove = nodeToMove;
    lg.nodeCost = nodeCost;

    printf("====liveness:\n");
    for (G_nodeList it = G_nodes(flow); it; it = it->tail) {
        G_node node = it->head;
        printCfgInfo(G_nodeInfo(node));
        // if (FG_def(node) == NULL) continue;
        Temp_tempList tempOut = G_look(liveOut, node);
        Temp_tempList tempIn = G_look(liveIn, node);
        printf("[out]\t");
        Temp_dumpList(stdout, tempOut);
        printf("[in]\t");
        Temp_dumpList(stdout, tempIn);
    }
    for (G_nodeList it = G_nodes(interference); it; it = it->tail) {
        G_node node = it->head;
        printf("node %d cost %f\n", Temp_getnum(Live_gtemp(node)),
               getCost(nodeCost, node));
    }
    return lg;
}

/**
 * Returns whether lhs is the same as rhs move.
 * Note that even if they are the same, they may have different tails
 */
bool moveEqual(Live_moveList lhs, Live_moveList rhs) {
    return lhs->src == rhs->src && lhs->dst == rhs->dst;
}

bool moveListIn(Live_moveList list, Live_moveList move) {
    for (Live_moveList it = list; it; it = it->tail)
        if (moveEqual(it, move)) return TRUE;
    return FALSE;
}

Live_moveList moveListUnion(Live_moveList lhs, Live_moveList rhs) {
    Live_moveList ret = NULL;
    for (Live_moveList r = lhs; r; r = r->tail)
        if (!moveListIn(ret, r)) ret = Live_MoveList(r->src, r->dst, ret);
    for (Live_moveList r = rhs; r; r = r->tail)
        if (!moveListIn(ret, r)) ret = Live_MoveList(r->src, r->dst, ret);
    return ret;
}

Live_moveList moveListJoin(Live_moveList lhs, Live_moveList rhs) {
    Live_moveList ret = NULL;
    for (Live_moveList lIt = lhs; lIt; lIt = lIt->tail) {
        G_node srcNode = lIt->src;
        G_node dstNode = lIt->dst;
        for (Live_moveList rIt = rhs; rIt; rIt = rIt->tail) {
            G_node rSrcNode = lIt->src;
            G_node rDstNode = lIt->dst;
            if (srcNode == rSrcNode && dstNode == rDstNode)
                ret = Live_MoveList(srcNode, dstNode, ret);
        }
    }
    return ret;
}

Live_moveList moveListDiff(Live_moveList lhs, Live_moveList rhs) {
    // {x| x in lhs and x not in rhs}
    Live_moveList ret = NULL;
    for (Live_moveList lIt = lhs; lIt; lIt = lIt->tail) {
        Live_moveList rIt = NULL;
        for (rIt = rhs; rIt; rIt = rIt->tail)
            if (moveEqual(lIt, rIt)) break;
        if (rIt == NULL) ret = Live_MoveList(lIt->src, lIt->dst, ret);
    }
    return ret;
}
void moveListDump(FILE *out, Live_moveList list) {
    for (Live_moveList iter = list; iter; iter = iter->tail) {
        fprintf(out, "t%d<-t%d ", Temp_getnum(G_nodeInfo(iter->dst)),
                Temp_getnum(G_nodeInfo(iter->src)));
    }
    fprintf(out, "\n");
}