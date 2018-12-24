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

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
	//your code here.
	G_graph graph = G_Graph();
	G_table gtable = G_empty();
	// instruction - node table
	Ins_table instr_node = Ins_empty();
	// lael - node table
	TAB_table label_node = TAB_empty();
	AS_instrList inslist = il;
	G_node prevnode = NULL;
	AS_instrList pending = NULL;
	/* 
	 * Add edge between two instructions
	 * * if jump instruction, add edge between targets and jump instruction
	 * * if not, add edge to previous one
	 */
	while (inslist) {
		G_node n = G_Node(graph, inslist->head);
		Ins_enter(instr_node, inslist->head, n);
		if (inslist->head->kind == I_LABEL) {
			TAB_enter(label_node, inslist->head->u.LABEL.label, n);
		}
		if (prevnode) {
			G_addEdge(prevnode, n);
		}
		prevnode = n;

		// add edge to jump target instruction
		if (inslist->head->kind == I_OPER) {
			bool ispending = FALSE;
			AS_targets astargets = inslist->head->u.OPER.jumps;
			Temp_labelList tars = NULL;
			if (astargets) tars = astargets->labels;

			while (tars) {
				G_node jump = TAB_look(label_node, tars->head);
				// if no node mapping to label, put the instruction to pending queue
				// add edge when all instruction has a node mapping to
				if (!jump && !ispending) {
					pending = AS_InstrList(inslist->head, pending);
				}
				else if (jump) {
					G_addEdge(n, jump);
				}
				tars = tars->tail;
			}
		}
		inslist = inslist->tail;
	}

	// deal with pending instruction
	AS_instrList cursor = pending;
	while (cursor) {
		G_node n = Ins_look(instr_node, cursor->head);
		G_nodeList succ = G_succ(n);

		AS_targets tgs = cursor->head->u.OPER.jumps;
		Temp_labelList tars = tgs->labels;
		while (tars) {
			G_node jump = TAB_look(label_node, tars->head);
			if (!jump) {
				fprintf(stderr, "label %s not found!", Temp_labelstring(tars->head));
				assert(0);
			}
			if (!G_inNodeList(jump, succ)) {
				G_addEdge(n, jump);
			}
			tars = tars->tail;
		}
		cursor = cursor->tail;
	}
	return graph;
}
