/*
 * flowgraph.h - Function prototypes to represent control flow graphs.
 */

#ifndef FLOWGRAPH_H
#define FLOWGRAPH_H

extern FILE *file;

void printAssem(AS_instr ins);

Temp_tempList FG_def(G_node n);
Temp_tempList FG_use(G_node n);
bool FG_isMove(G_node n);
G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f);

#endif

#if _DEBUG_
void dump_templist(FILE *file, Temp_tempList list);
void printAssem(AS_instr ins);
void FG_dump(FILE *file, G_graph graph);
#endif