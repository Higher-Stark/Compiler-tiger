#ifndef LIVENESS_H
#define LIVENESS_H

typedef struct Live_moveList_ *Live_moveList;
struct Live_moveList_ {
	G_node src, dst;
	Live_moveList tail;
};

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail);

struct Live_graph {
	G_graph graph;
	Live_moveList moves;
};
Temp_temp Live_gtemp(G_node n);

struct Live_graph Live_liveness(G_graph flow);

/* 
 * some set operation
 */
bool inMoveList(Live_moveList mvlist, G_node src, G_node dst);
bool set_equal(Temp_tempList left, Temp_tempList right);
Temp_tempList difference(Temp_tempList left, Temp_tempList right);
Temp_tempList intersect(Temp_tempList left, Temp_tempList right);
Temp_tempList aggregate(Temp_tempList left, Temp_tempList right);
bool has(Temp_tempList tl, Temp_temp t);
#endif

#ifndef _DEBUG_
#define _DEBUG_ 1
#endif

#if _DEBUG_

extern FILE *file;
void Live_mdump(FILE *out, Live_moveList mvList);
/*
 * Live move dump
 */
void Live_mprint(G_node src, G_node dst);
#endif