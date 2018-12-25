#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"
#include "temp.h"

extern int ASSEMLEN;
#define K (F_reg_amount - 2)

static char *avail_regs[14] = {"%rax", "%rcx", "%rdx", "%rbx",
																 "%rsi", "%rdi", "%r8", "%r9", 
																 "%r10", "%r11", "%r12", "%r13", 
																 "%r14", "%r15"};
int IndexColor(string c);
// TODO: initialization
// static G_graph adjSet;				// temps conflict graph
static TAB_table degree; 			// G_node <-> degree
static TAB_table moveList;		// G_node <-> move instruction
static TAB_table alias;				// G_node <-> G_node  (combined)
static Temp_map color;				// G_node <-> color

static G_nodeList precolored;				// hard registers of machine
static G_nodeList initial;					// neither colored nor handled
static G_nodeList simplifyWorklist;	// low degree and no move related
static G_nodeList freezeWorklist;		// low degree and move related
static G_nodeList spillWorklist;		// high degree
static G_nodeList spilledNodes;			// nodes to be spilled
static G_nodeList coalescedNodes;		// set of coalesced nodes
static G_nodeList coloredNodes;			// colored nodes
static G_nodeList selectStack;			// nodes removed from graph

static Live_moveList coalescedMoves;		// coalesced moves
static Live_moveList constrainedMoves;	// src conflict with dest moves
static Live_moveList frozenMoves;				// not to be comblined moves
static Live_moveList worklistMoves;			// may be combined moves in the future
static Live_moveList activeMoves;				// not ready to combine moves

static G_nodeList newTemps;		// temps come from spill

#if _DEBUG_
void degree_print(G_node key, int value);
void RA_degreeDump();
void RA_worklistMovesDump();
#endif

bool isPrecolored(G_node n);

void Build(AS_instrList il, struct Live_graph *live);
void AddEdge(G_node u, G_node v);
void MakeWorkList();
G_nodeList Adjacent(G_node n);
Live_moveList NodeMoves(G_node n);
bool MoveRelated(G_node n);
void Simplify();
void DecrementDegree(G_node m);
void EnableMoves(G_nodeList nodes);
void Coalesce();
void AddWorkList(G_node u);
bool OK(G_node t, G_node r);
bool Conservative(G_nodeList nodes);
G_node GetAlias(G_node n);
void Combine(G_node u, G_node v);
void Freeze();
void FreezeMoves(G_node u);
void SelectSpill();
void AssignColors();
AS_instrList RewriteProgram(AS_instrList il_old, F_frame f, G_graph g_tmp);

G_nodeList N_aggregate(G_nodeList u, G_nodeList v);
G_nodeList N_intersect(G_nodeList u, G_nodeList v);
G_nodeList N_difference(G_nodeList u, G_nodeList v);
G_nodeList N_remove(G_nodeList list, G_node n);
bool N_in_node_list(G_nodeList list, G_node n);

Live_moveList L_aggregate(Live_moveList u, Live_moveList v);
Live_moveList L_intersect(Live_moveList u, Live_moveList v);
Live_moveList L_difference(Live_moveList u, Live_moveList v);
Live_moveList L_remove(Live_moveList list, G_node src, G_node dst);

AS_instrList AS_aggregate(AS_instrList u, AS_instrList v);
bool AS_in(AS_instrList list, AS_instr ins);

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	//your code here
	bool complete = FALSE;
	struct RA_result ret;
	F_tempMap = Temp_layerMap(F_tempMap, F_registerMap());
	color = F_tempMap;

	while (!complete) {
		complete = TRUE;

		/* Construct Flow graph */
		G_graph g_flow = FG_AssemFlowGraph(il, f);

		/* Livness Analysis */
		struct Live_graph g_live = Live_liveness(g_flow);

		for (G_nodeList l = G_nodes(g_live.graph); l; l = l->tail) {
			if (!isPrecolored(l->head))
				initial = N_aggregate(initial, G_NodeList(l->head, NULL));
		}
		simplifyWorklist = NULL;
		freezeWorklist = NULL;
		spillWorklist = NULL;
		spilledNodes = NULL;
		coalescedNodes = NULL;
		coloredNodes = NULL;
		selectStack = NULL;

		coalescedMoves = NULL;
		constrainedMoves = NULL;
		frozenMoves = NULL;
		worklistMoves = g_live.moves;
		activeMoves = NULL;

		degree = G_empty();
		moveList = G_empty();
		alias = G_empty();
		color = F_tempMap;

		Build(il, &g_live);

		MakeWorkList();

#if _DEBUG_
		RA_worklistMovesDump();
		RA_degreeDump();
#endif

		while (simplifyWorklist != NULL || worklistMoves != NULL || freezeWorklist != NULL || spillWorklist != NULL ) {
			if (simplifyWorklist) Simplify();
			else if (worklistMoves) Coalesce();
			else if (freezeWorklist) Freeze();
			else if (spillWorklist) SelectSpill();

#if _DEBUG_
			RA_worklistMovesDump();
			RA_degreeDump();
#endif

		}	

		AssignColors();

		if (spilledNodes) {
			complete = FALSE;
			il = RewriteProgram(il, f, g_live.graph);
		}
	}
	ret.coloring = color;
	ret.il = il;
	return ret;
}

/*
 * Function: isPrecolored
 * Description: if the node is a hard register
 */
bool isPrecolored(G_node n)
{
	Temp_temp t = Live_gtemp(n);
	for (Temp_tempList l = hardregisters(); l; l = l->tail) {
		if (t == l->head) return TRUE;
	}
	return FALSE;
}

/*
 * Function: Build
 * Description: initialize worklistMoves with liveness result
 */
void Build(AS_instrList il, struct Live_graph *live)
{
	worklistMoves = live->moves;
	for (AS_instrList ins = il; ins; ins = ins->tail) {
		if (ins->head->kind == I_MOVE) {
			// move related temps
			Temp_tempList mvRtdtmps = aggregate(ins->head->u.MOVE.src, ins->head->u.MOVE.dst);
			for (Temp_tempList mvtmps = mvRtdtmps; mvtmps; mvtmps = mvtmps->tail){
				AS_instrList relatedIns = TAB_look(moveList, mvtmps->head);
				relatedIns = AS_InstrList(il->head, relatedIns);
				TAB_enter(moveList, mvtmps, relatedIns);
			}
		}
	}
	// initialize degree table
	for (G_nodeList l = G_nodes(live->graph); l; l = l->tail) {
		Temp_temp t = Live_gtemp(l->head);
		int d = G_degree(l->head);
		TAB_enter(degree, l->head, (void *)d);
	}
}

/*
 * Function: AddEdge
 * Description: add edge between node u and node v
 */
void AddEdge(G_node u, G_node v)
{
	if (!G_inNodeList(u, G_adj(v)) && u != v) {
		G_addEdge(u, v);
		if (!isPrecolored(u)) {
			int d = (int) TAB_look(degree, u);
			TAB_enter(degree, u, (void *)(d + 1));
		}
		if (!isPrecolored(v)) {
			int d = (int) TAB_look(degree, v);
			TAB_enter(degree, v, (void *)(d + 1));
		}
	}
}

/*
 * Function: MakeWorklist
 * Description: classsify nodes by their degree and 
 * 							add to corresponding list
 */
void MakeWorkList()
{
	for (G_nodeList n = initial; n; n = n->tail) {
		int d = (int) TAB_look(degree, n->head);
		if (d >= K)
			spillWorklist = N_aggregate(spillWorklist, G_NodeList(n->head, NULL));
		else if (MoveRelated(n->head))
			freezeWorklist = N_aggregate(freezeWorklist, G_NodeList(n->head, NULL));
		else
			simplifyWorklist = N_aggregate(simplifyWorklist, G_NodeList(n->head, NULL));
	}
}

/* 
 * Function: Adjacent
 * Description: return adjacent nodes
 */
G_nodeList Adjacent(G_node n){
	return N_difference(G_adj(n),
											N_aggregate(selectStack, coalescedNodes));
}

/* 
 * Function: NodeMoves
 * Description: find available moves that can be combined
 */
Live_moveList NodeMoves(G_node n)
{
	Live_moveList mvList = TAB_look(moveList, n);
	return L_intersect(mvList, L_aggregate(activeMoves, worklistMoves));
}

/* 
 * Function: MoveRelated
 * Description: whether node n is related to some move instruction
 */
bool MoveRelated(G_node n)
{
	return NodeMoves(n) == NULL;
}

/*
 * Function: Simplify
 * Description: remove nodes in simplify Work list and push to select stack
 */
void Simplify()
{
	for (G_nodeList l = simplifyWorklist; l; l = l->tail) {
		selectStack = G_NodeList(l->head, selectStack);
		for (G_nodeList adj = Adjacent(l->head); adj; adj = adj->tail) {
			DecrementDegree(adj->head);
		}
	}
	simplifyWorklist = NULL;
}

/* 
 * Function: DecrementDegree
 * Description: decrement node's degree by 1
 */
void DecrementDegree(G_node m)
{
	int d = (int) TAB_look(degree, m);
	TAB_enter(degree, m, (void *)(d - 1));
	if (d == K) {
		EnableMoves(N_aggregate(G_NodeList(m, NULL), Adjacent(m)));
		spillWorklist = N_remove(spillWorklist, m);
		if (MoveRelated(m)) freezeWorklist = N_aggregate(freezeWorklist, G_NodeList(m, NULL));
		else simplifyWorklist = N_aggregate(simplifyWorklist, G_NodeList(m, NULL));
	}
}

/*
 * Function: EnableMoves
 * Description: remove the move from activeMoves and add to worklistMoves
 */
void EnableMoves(G_nodeList nodes)
{
	for (G_nodeList l = nodes; l; l = l->tail) {
		for (Live_moveList m = NodeMoves(l->head); m; m = m->tail) {
			if (inMoveList(activeMoves, m->src, m->dst)) {
				L_remove(activeMoves, m->src, m->dst);
				worklistMoves = L_aggregate(worklistMoves, Live_MoveList(m->src, m->dst, NULL));
			}
		}
	}
}
/* 
 * Function: Coalesce
 * Description: 
 */
void Coalesce() 
{
	for (Live_moveList m = worklistMoves; m; m = m->tail) {
		G_node x = GetAlias(m->src);
		G_node y = GetAlias(m->dst);
		G_node u = NULL, v = NULL;
		if (isPrecolored(y)) {
			u = y; v = x;
		}
		else {
			u = x; v = y;
		}
		L_remove(worklistMoves, m->src, m->dst);
		if (u == v) {
			coalescedMoves = L_aggregate(coalescedMoves, Live_MoveList(m->src, m->dst, NULL));
			AddWorkList(u);
		}
		else if (isPrecolored(v) || G_inNodeList(u, G_adj(v))) {
			constrainedMoves = L_aggregate(constrainedMoves, Live_MoveList(m->src, m->dst, NULL));
			AddWorkList(u);
			AddWorkList(v);
		}
		else if (isPrecolored(u)) {
			G_nodeList adjs = Adjacent(v);
			bool flag = TRUE;
			for (G_nodeList adjs = Adjacent(v); adjs; adjs = adjs->tail) {
				flag = flag && OK(adjs->head, u);
			}
			if (flag || !isPrecolored(u) && 
			Conservative(N_aggregate(Adjacent(u), Adjacent(v)))) {
				coalescedMoves = L_aggregate(coalescedMoves, Live_MoveList(m->src, m->dst, NULL));
				Combine(u, v);
				AddWorkList(u);
			}
			else goto elsee;
		}
		else {
		elsee:
			activeMoves = L_aggregate(activeMoves, Live_MoveList(m->src, m->dst, NULL));
		}
	}
}

/* 
 * Function: AddWorkList
 * Description: add node to work list
 */
void AddWorkList(G_node u)
{
	int d = (int) TAB_look(degree, u);
	if (!G_inNodeList(u, freezeWorklist) && ! MoveRelated(u) && d < K) {
		freezeWorklist = N_remove(freezeWorklist, u);
		simplifyWorklist = N_aggregate(simplifyWorklist, G_NodeList(u, NULL));
	}
}

/*
 * Function: OK
 * Description: 
 */
bool OK(G_node t, G_node r)
{
	int d = (int) TAB_look(degree, t);
	bool ret = d < K;
	ret = ret || isPrecolored(t);
	ret = ret || G_inNodeList(r, G_adj(t));
	return ret;
}

/*
 * Function: Conservative
 * Description: if the node is conservative
 */
bool Conservative(G_nodeList nodes)
{
	int k = 0;
	for (G_nodeList l = nodes; l; l = l->tail) {
		int d = (int) TAB_look(degree, l->head);
		if (d >= K) k++;
	}
	return k < K;
}

/*
 * Function: GetAlias
 * Description: which node this node combined to
 */
G_node GetAlias(G_node n)
{
	if (G_inNodeList(n, coalescedNodes)) {
		G_node m = TAB_look(alias, n);
		return GetAlias(m);
	}
	else return n;
}

/*
 * Function: Combine
 * Description: combine two nodes into one node in graph
 * 							add into alias table
 */
void Combine(G_node u, G_node v)
{
	if (G_inNodeList(v, freezeWorklist)) {
		freezeWorklist = N_remove(freezeWorklist, v);
	}
	else spillWorklist = N_remove(spillWorklist, v);
	coalescedNodes = N_aggregate(coalescedNodes, G_NodeList(v, NULL));
	TAB_enter(alias, v, u);
	AS_instrList u_moves = TAB_look(moveList, u);
	AS_instrList v_moves = TAB_look(moveList, v);
	AS_instrList uv_moves = AS_aggregate(u_moves, v_moves);
	TAB_enter(moveList, u, uv_moves);
	EnableMoves(G_NodeList(v, NULL));
	for (G_nodeList adjs = Adjacent(v); adjs; adjs = adjs->tail) {
		AddEdge(adjs->head, u);
		DecrementDegree(adjs->head);
	}
	int d = (int) TAB_look(degree, u);
	if (d >= K && G_inNodeList(u, freezeWorklist)) {
		freezeWorklist = N_remove(freezeWorklist, u);
		spillWorklist = N_aggregate(spillWorklist, G_NodeList(u, NULL));
	}
}

/* 
 * Function: Freeze
 * Description: do Freeze
 */
void Freeze()
{
	G_node u = NULL;
	int deg = __INT_MAX__;
	for (G_nodeList nl = freezeWorklist; nl; nl = nl->tail) {
		if (!MoveRelated(nl->head)) continue;
		int dd = (int) TAB_look(degree, nl->head);
		if (dd < deg) {
			u = nl->head; 
			deg = dd;
		}
	}
	N_remove(freezeWorklist, u);
	simplifyWorklist = N_aggregate(simplifyWorklist, G_NodeList(u, NULL));
	FreezeMoves(u);
}

/* 
 * Function: FreezeMoves
 * Description: Freeze moves of node u
 */
void FreezeMoves(G_node u)
{
	for (Live_moveList m = NodeMoves(u); m; m = m->tail) {
		G_node x = m->src, y = m->dst;
		G_node v = NULL;
		if (GetAlias(y) == GetAlias(x)) v = GetAlias(x);
		else v = GetAlias(y);
		activeMoves = L_remove(activeMoves, m->src, m->dst);
		frozenMoves = L_aggregate(frozenMoves, Live_MoveList(m->src, m->dst, NULL));
		int d = (int) TAB_look(degree, v);
		if (NodeMoves(v) == NULL && d < K) {
			freezeWorklist = N_remove(freezeWorklist, v);
			simplifyWorklist = N_remove(simplifyWorklist, v);
		}
	}
}

/* 
 * Function SelectSpill
 * Description: select a node and spill
 */
void SelectSpill()
{
	G_node m = NULL;
	{
		int d = 0;
		G_node tmp = NULL;
		int dtmp = 0;
		/*
		 * If a node is in newTemp, which come from previous spill, 
		 * remain a secondary choice.
		 * Nodes with highest degree and not in newTemp got first priority
		 */
		for (G_nodeList l = spillWorklist; l; l = l->tail) {
			if (G_inNodeList(l->head, newTemps)) {
				int dd = (int) TAB_look(degree, l->head);
				if (dd > dtmp) {
					dtmp = dd;
					tmp = l->head;
				}
			}
			else {
				int dd = (int) TAB_look(degree, l->head);
				if (dd > d) {
					d = dd;
					m = l->head;
				}
			}
		}
		
		if (!(m || tmp)) {
			fprintf(stderr, "no proper temp selected to spill");
		} 
		else if (!m && tmp) m = tmp;
	}
	assert(m);
	spillWorklist = N_remove(spillWorklist, m);
	simplifyWorklist = N_aggregate(simplifyWorklist, G_NodeList(m, NULL));
	FreezeMoves(m);
}
/* 
 * Function: AssignColors
 * Description: assign color for nodes
 */
void AssignColors()
{
	// G_nodeList selectStack = selectStack;
	bool okColors[K];
	while (selectStack) {
		for (int i = 0; i != K; i++) {
			okColors[i] = TRUE;
		}
		G_node n = selectStack->head;
		for (G_nodeList w = G_adj(n); w; w = w->tail) {
			G_node alias_node = GetAlias(w->head);
			if (G_inNodeList(alias_node, coloredNodes) || isPrecolored(alias_node)) {
				string cc = (string) Temp_look(color, (Temp_temp) G_nodeInfo(alias_node));
				int color_idx = IndexColor(cc);
				okColors[color_idx] = FALSE;
			}
		}
		// TODO: find available color
		int available = 0;
		while (available < K && !okColors[available]) {
			available++;
		}
		if (available >= K) {
			spilledNodes = N_aggregate(spilledNodes, G_NodeList(n, NULL));
		}
		else {
			coloredNodes = N_aggregate(coloredNodes, G_NodeList(n, NULL));
			string c = avail_regs[available];
			Temp_enter(color, (Temp_temp) G_nodeInfo(GetAlias(n)), c);
		}
		selectStack = selectStack->tail;
	}
	for (G_nodeList n = coalescedNodes; n; n = n->tail) {
		string c = Temp_look(color, (Temp_temp) G_nodeInfo(GetAlias(n->head)));
		Temp_enter(color, (Temp_temp) G_nodeInfo(n->head), c);
	}
}

/*
 * Function: RewriteProgram
 * Description: allocate space on frame for each spilled node, 
 * 							create a new temp every time before access and after write,
 * 							replace old temp with new temps
 */
AS_instrList RewriteProgram(AS_instrList il_old, F_frame f, G_graph g_tmp)
{
	AS_instrList il_new = NULL;
	for (G_nodeList n = spilledNodes; n; n = n->tail) {
		F_access acc = F_allocLocal(f, TRUE);
		int offset = F_inFrameOffset(acc);
		/*
		 *   If temp is used, load from stack before using. 
		 * Replace old temp in src with a new temp.
		 *   If is defined, write to stack after definition.
		 * Replace old temp in dest with the new one.
		 *   If old temp shows up both in use and dst, one 
		 * and only one new temp should replace it.
		 */
		for (AS_instrList i = il_old; i; i = i->tail) {
			bool read = FALSE;
			bool write = FALSE;
			Temp_tempList *psrc = NULL, *pdst = NULL;
			switch(i->head->kind) {
				case I_MOVE: {
					if (inTemplist(i->head->u.MOVE.src, G_nodeInfo(n->head))) 
						{ read = TRUE; psrc = &(i->head->u.MOVE.src); }
					if (inTemplist(i->head->u.MOVE.dst, G_nodeInfo(n->head))) 
						{ write = TRUE; pdst = &(i->head->u.MOVE.dst); }
					break;
				}
				case I_OPER: {
					if (inTemplist(i->head->u.OPER.src, G_nodeInfo(n->head))) 
						{ read = TRUE; psrc = &(i->head->u.OPER.src); }
					if (inTemplist(i->head->u.OPER.dst, G_nodeInfo(n->head))) 
						{ write = TRUE; pdst = &(i->head->u.OPER.dst); }
					break;
				}
			}

			AS_instr newins = NULL;
			Temp_temp tt = NULL;
			if (read) {
				char buf[ASSEMLEN];
				tt = Temp_newtemp();
				sprintf(buf, "movq\t%d(%%rbp), `d0", offset);
				newins = AS_Move(String(buf),
												 Temp_TempList(tt, NULL),
												 Temp_TempList(F_FP(), NULL));
				il_new = AS_splice(il_new, AS_InstrList(newins, NULL));
				newins = NULL;
			}

			if (tt) {
				*psrc = Temp_Replace(*psrc, G_nodeInfo(n->head), tt);
			}
			if (write) {
				if (!tt) tt = Temp_newtemp();
				*pdst = Temp_Replace(*pdst, G_nodeInfo(n->head), tt);
				char buf[ASSEMLEN];
				sprintf(buf, "movq\t`s0, %d(%%rbp)", offset);
				newins = AS_Move(String(buf),
												 Temp_TempList(F_FP(), NULL),
												 Temp_TempList(tt, NULL));
			}
			il_new = AS_splice(il_new, AS_InstrList(i->head, NULL));
			if (newins) {
				AS_splice(il_new, AS_InstrList(newins, NULL));
			}

			G_node ttnode = G_Node(g_tmp, tt);
			newTemps = N_aggregate(newTemps, G_NodeList(ttnode, NULL));
		}
	}
	spilledNodes = NULL;
	initial = N_aggregate(coloredNodes, N_aggregate(coalescedNodes, newTemps));
	coloredNodes = NULL;
	coalescedNodes = NULL;

	return il_new;
}

/* ------------------------------------------------------------------------- */
/*
 * Function: N_aggregate
 * Description: u ∪ v
 */
G_nodeList N_aggregate(G_nodeList u, G_nodeList v)
{
	G_nodeList ret = NULL;
	G_nodeList rtail = NULL;
	for (G_nodeList l = u; l; l = l->tail) {
		if (ret) {
			rtail->tail = G_NodeList(l->head, NULL);
			rtail = rtail->tail;
		}
		else {
			ret = G_NodeList(l->head, NULL);
			rtail = ret;
		}
	}
	for (G_nodeList l = v; l; l = l->tail) {
		if (G_inNodeList(l->head, ret)) continue;
		if (ret) {
			rtail->tail = G_NodeList(l->head, NULL);
			rtail = rtail->tail;
		}
		else {
			ret = G_NodeList(l->head, NULL);
			rtail = ret;
		}
	}
	return ret;
}

/* 
 * Function: N_intersect
 * Description: u ∩ v
 */
G_nodeList N_intersect(G_nodeList u, G_nodeList v)
{
	G_nodeList ret = NULL;
	G_nodeList rtail = NULL;
	for (G_nodeList l = u; l; l = l->tail) {
		if (G_inNodeList(l->head, v)) {
			if (ret)
			{
				rtail->tail = G_NodeList(l->head, NULL);
				rtail = rtail->tail;
			}
			else
			{
				ret = G_NodeList(l->head, NULL);
				rtail = ret;
			}
		}
	}
	return ret;
}

/* 
 * Function: N_difference
 * Description: u / v
 */
G_nodeList N_difference(G_nodeList u, G_nodeList v)
{
	G_nodeList ret = NULL;
	G_nodeList rtail = NULL;
	for (G_nodeList l = u; l; l = l->tail) {
		if (!G_inNodeList(l->head, v)) {
			if (ret)
			{
				rtail->tail = G_NodeList(l->head, NULL);
				rtail = rtail->tail;
			}
			else
			{
				ret = G_NodeList(l->head, NULL);
				rtail = ret;
			}
		}
	}
	return ret;
}

/* 
 * Function: N_remove
 * Description: remove n from list
 */
G_nodeList N_remove(G_nodeList list, G_node n)
{
	G_nodeList ret = NULL;
	G_nodeList rtail = NULL;
	for (G_nodeList l = list; l; l = l->tail) {
		if (l->head == n) continue;
		if (ret) {
			rtail->tail = G_NodeList(l->head, NULL);
			rtail = rtail->tail;
		}
		else {
			ret = G_NodeList(l->head, NULL);
			rtail = ret;
		}
	}
	return ret;
}

/* 
 * Function: N_in_node_list
 * Description: whether n is in the list
 */
bool N_in_node_list(G_nodeList list, G_node n)
{
	for (G_nodeList l = list; l; l = l->tail) {
		if (l->head == n) return TRUE;
	}
	return FALSE;
}

/* ----------------------------------------------------- */

Live_moveList L_aggregate(Live_moveList u, Live_moveList v)
{
	Live_moveList ret = NULL;
	Live_moveList rtail = NULL;
	for (Live_moveList l = u; l; l = l->tail) {
		if (ret) {
			rtail->tail = Live_MoveList(l->src, l->dst, NULL);
			rtail = rtail->tail;
		}
		else {
			ret = Live_MoveList(l->src, l->dst, NULL);
			rtail = ret;
		}
	}
	for (Live_moveList l = v; l; l = l->tail) {
		if (inMoveList(ret, l->src, l->dst)) continue;
		if (ret) {
			rtail->tail = Live_MoveList(l->src, l->dst, NULL);
			rtail = rtail->tail;
		}
		else {
			ret = Live_MoveList(l->src, l->dst, NULL);
			rtail = ret;
		}
	}
	return ret;

}
Live_moveList L_intersect(Live_moveList u, Live_moveList v)
{
	Live_moveList ret = NULL;
	Live_moveList rtail = NULL;
	for (Live_moveList l = u; l; l = l->tail) {
		if (inMoveList(v, l->src, l->dst)) {
			if (ret)
			{
				rtail->tail = Live_MoveList(l->src, l->dst, NULL);
				rtail = rtail->tail;
			}
			else
			{
				ret = Live_MoveList(l->src, l->dst, NULL);
				rtail = ret;
			}
		}
	}
	return ret;
}
Live_moveList L_difference(Live_moveList u, Live_moveList v)
{
	Live_moveList ret = NULL;
	Live_moveList rtail = NULL;
	for (Live_moveList l = u; l; l = l->tail) {
		if (!inMoveList(v, l->src, l->dst)) {
			if (ret)
			{
				rtail->tail = Live_MoveList(l->src, l->dst, NULL);
				rtail = rtail->tail;
			}
			else
			{
				ret = Live_MoveList(l->src, l->dst, NULL);
				rtail = ret;
			}
		}
	}
	return ret;
}
Live_moveList L_remove(Live_moveList list, G_node src, G_node dst)
{
	Live_moveList ret = NULL;
	Live_moveList rtail = NULL;
	for (Live_moveList l = list; l; l = l->tail) {
		if (l->src == src && l->dst == dst) continue;
		if (ret) {
			rtail->tail = Live_MoveList(l->src, l->dst, NULL);
			rtail = rtail->tail;
		}
		else {
			ret = Live_MoveList(l->src, l->dst, NULL);
			rtail = ret;
		}
	}
	return ret;
}

/* ------------------------------------------------------ */

AS_instrList AS_aggregate(AS_instrList u, AS_instrList v) 
{
	AS_instrList ret = NULL;
	AS_instrList rtail = NULL;
	for (AS_instrList ul = u; ul; ul = ul->tail) {
		if (ret) {
			rtail->tail = AS_InstrList(ul->head, NULL);
			rtail = rtail->tail;
		}
		else {
			ret = AS_InstrList(ul->head, NULL);
			rtail = ret;
		}
	}

	for (AS_instrList vl = v; vl; vl = vl->tail) {
		if (!AS_in(ret, vl->head)) {
			if (ret) {
				rtail->tail = AS_InstrList(vl->head, NULL);
				rtail = rtail->tail;
			}
			else {
				ret = AS_InstrList(vl->head, NULL);
				rtail = ret;
			}
		}
	}
	return ret;
}

bool AS_in(AS_instrList list, AS_instr ins) 
{
	for (AS_instrList l = list; l; l = l->tail) {
		if (l->head == ins) return TRUE;
	}
	return FALSE;
}

int IndexColor(string c)
{
	for (int i = 0; i != K; i++) {
		if (avail_regs[i] == c) return i;
	}
	return -1;
}

#if _DEBUG_
void degree_print(G_node key, int value)
{
	Temp_temp t = G_nodeInfo(key);
	if (isPrecolored(key)) {
		string s = Temp_look(color, G_nodeInfo(key));
		fprintf(file, "| %s | %d |\n", s, value);
	}
	fprintf(file, "| t<%d> | %d |\n", Temp_int(G_nodeInfo(key)), value);
}

void RA_degreeDump()
{
	file = fopen("__DEBUG_RA.md", "a");
	fprintf(file, "## Degree table\n");
	fprintf(file, "| Node(Temp) | Degree |\n");
	fprintf(file, "| :--: | --: |\n");
	TAB_dump(degree, (void (*)(void *, void *))degree_print);
	fprintf(file, "--------------\n");
	fclose(file);
}

void RA_worklistMovesDump()
{
		file = fopen("__DEBUG_RA.md", "a");
		fprintf(file, "# Register Allocation\n");
		fprintf(file, "## work list moves\n");
		fprintf(file, "| From | To |\n");
		fprintf(file, "| :--: | :--: |\n");
		Live_mdump(file, worklistMoves);
		fprintf(file, "--------------------\n");
		fclose(file);
}
#endif