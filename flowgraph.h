/*
 * flowgraph.h - Function prototypes to represent control flow graphs.
 */

#ifndef FLOWGRAPH_H
#define FLOWGRAPH_H

#include "frame.h"
#include "graph.h"

Temp_tempList FG_def(G_node n);
Temp_tempList FG_use(G_node n);
/**
 * Returns whether n irepresents a MOVE instruction
 */
bool FG_isMove(G_node n);
/**
 * Takes a list of instructions and returns a flow graph in which the info of
 * each G_node is actually a pointer to an AS_instr
 */
G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f);

#endif
