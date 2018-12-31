#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

#if _DEBUG_
FILE *file = NULL;

void FG_dump(FILE *file, G_graph graph)
{
	fprintf(file, "## Flow Graph\n");
	fprintf(file, "| Node index | Node class | Assembly | def | use | successor |\n");
	fprintf(file, "| ---: | :----: | :-- | :-- | :-- | :--- |\n");
	G_show(file, G_nodes(graph), (void (*)(void *))printAssem);
	fprintf(file, "-------------------------\n");
}

void dump_templist(FILE *file, Temp_tempList list)
{
	for (Temp_tempList l = list; l; l = l->tail) {
		if (inTemplist(hardregisters(), l->head)) {
			string s = Temp_look(F_registerMap(), l->head);
			fprintf(file, "%s, ", s);
		}
		else {
			fprintf(file, "t<%d>, ", Temp_int(l->head));
		}
	}
}

void printAssem(AS_instr ins)
{
	switch(ins->kind) {
		case I_LABEL: {
			fprintf(file, " Label | %s | | |", Temp_labelstring(ins->u.LABEL.label));
			return;
		}
		case I_MOVE: {
			fprintf(file, " MOVE | %s | ", ins->u.MOVE.assem);
			dump_templist(file, ins->u.MOVE.dst);
			fprintf(file, " | ");
			dump_templist(file, ins->u.MOVE.src);
			fprintf(file, " |");
			return;
		}
		case I_OPER: {
			fprintf(file, " OPER | %s |", ins->u.MOVE.assem);
			dump_templist(file, ins->u.OPER.dst);
			fprintf(file, " | ");
			dump_templist(file, ins->u.OPER.src);
			fprintf(file, " |");
			return;
		}
	}
	assert(0);
}
#endif

Temp_tempList FG_def(G_node n) {
	//your code here.
	AS_instr ins =  (AS_instr)G_nodeInfo(n);
	switch(ins->kind) {
		case I_OPER: return ins->u.OPER.dst;
		case I_MOVE: return ins->u.MOVE.dst;
		case I_LABEL: return NULL;
	}
	assert(0);
	return NULL;
}

Temp_tempList FG_use(G_node n) {
	//your code here.
	AS_instr ins = (AS_instr) G_nodeInfo(n);
	switch(ins->kind) {
		case I_OPER: return ins->u.OPER.src;
		case I_MOVE: return ins->u.MOVE.src;
		case I_LABEL: return NULL;
	}
	assert(0);
	return NULL;
}

bool FG_isMove(G_node n) {
	//your code here.
	AS_instr ins = (AS_instr) G_nodeInfo(n);
	return ins->kind == I_MOVE;
}

typedef struct TAB_table_ *Ins_table;

Ins_table Ins_empty(void)
{
	return TAB_empty();
}

void Ins_enter(Ins_table t, AS_instr ins, void *v)
{
	TAB_enter(t, ins, v);
}

void *Ins_look(Ins_table t, AS_instr ins)
{
	return TAB_look(t, ins);
}

G_nodeList push(G_nodeList q, G_node n)
{
	return G_NodeList(n, q);
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
	//your code here.
	G_graph graph = G_Graph();
	// jump nodes
	G_nodeList queue = NULL;
	// lael - node table
	TAB_table labelTab = TAB_empty();
	/* 
	 * Add edge between two instructions
	 * * if jump instruction, add edge between targets and jump instruction
	 * * if not, add edge to previous one
	 */
	G_node last = NULL;
	for (AS_instrList inss = il; inss; inss = inss->tail) {
		G_node n = G_Node(graph, inss->head);
		/* Label */
		if (inss->head->kind == I_LABEL) {
			TAB_enter(labelTab, inss->head->u.LABEL.label, n);
			if (last)
				G_addEdge(last, n);
			last = n;
		}
		/* jump and non-jump */
		else if (inss->head->kind == I_OPER) {
			if (last)
				G_addEdge(last, n);
			last = n;
			if (inss->head->u.OPER.jumps) {
				queue = push(queue, n);
				last = NULL;
			}
		}
		/* Move */
		else {
			if (last) G_addEdge(last, n);
			last = n;
		}
	}
	while (queue) {
		G_node n = queue->head;
		queue = queue->tail;
		AS_instr ins = G_nodeInfo(n);
		Temp_labelList labelList = ins->u.OPER.jumps->labels;
		for (Temp_labelList labels = labelList; labels; labels = labels->tail) {
			G_node target = (G_node) TAB_look(labelTab, labels->head);
			assert(G_inNodeList(target, G_nodes(graph)));
			G_addEdge(n, target);
		}
	}

#if _DEBUG_
	file = fopen("__DEBUG_.md", "a");
	FG_dump(file, graph);
	fclose(file);
#endif
	return graph;
}
