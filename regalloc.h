/* function prototype from regalloc.c */

#ifndef REGALLOC_H
#define REGALLOC_H

#include "temp.h"
#include "frame.h"
#include "assem.h"

struct RA_result {
    Temp_map coloring;
    AS_instrList il;
};
struct RA_result RA_regAlloc(F_frame f, AS_instrList il, int cnt);

#endif
