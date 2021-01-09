/*
 * color.h - Data structures and function prototypes for coloring algorithm
 *             to determine register allocation.
 */

#ifndef COLOR_H
#define COLOR_H

#include "graph.h"
#include "liveness.h"

struct COL_result {
    Temp_map coloring;     // description of register allocation
    Temp_tempList spills;  // spilled registers
};

/**
 * Given the interference graph, precolored nodes and machine registers, just do
 * the graph coloring
 * @param{initial} pre-colored nodes
 */
struct COL_result COL_color(struct Live_graph ig, Temp_map initial,
                            Temp_tempList regs);

#endif
