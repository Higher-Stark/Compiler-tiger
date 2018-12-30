#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"

#if _DEBUG_
/*
 * @key: node of control flow
 * @value: temp list of the node
 */
void dump_map(G_node key, Temp_tempList *value)
{
	fprintf(file, "| %d | %p |\n", G_Key(key), *value);
}
#endif

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}

static void enterLiveMap(G_table t, G_node flowNode, Temp_tempList temps) 
{
	G_enter(t, flowNode, temps);
}

static Temp_tempList lookupLiveMap(G_table t, G_node flownode)
{
	return (Temp_tempList) G_look(t, flownode);
}

/*
 * Function: Live_gtemp
 * Description: get the Temp node n stands for
 * Temp is the info of the node
 */
Temp_temp Live_gtemp(G_node n) {
	return (Temp_temp)G_nodeInfo(n);
}

/*
 * Function: has
 * Description: in templist
 */
bool has(Temp_tempList tl, Temp_temp t)
{
	for (Temp_tempList l = tl; l; l = l->tail) {
		if (t == l->head) return TRUE;
	}
	return FALSE;
}

/* 
 * Function: aggregate
 * Description: 并集
 */
Temp_tempList aggregate(Temp_tempList left, Temp_tempList right)
{
	Temp_tempList ret = NULL;
	Temp_tempList tail = NULL;
	for (Temp_tempList l = left; l; l = l->tail) {
		if (ret) {
			tail->tail = Temp_TempList(l->head, NULL);
			tail = tail->tail;
		}
		else {
			ret = Temp_TempList(l->head, NULL);
			tail = ret;
		}
	}

	for (Temp_tempList r = right; r; r = r->tail) {
		if (!has(ret, r->head)) {
			if (ret) {
				tail->tail = Temp_TempList(r->head, NULL);
				tail = tail->tail;
			}
			else {
				ret = Temp_TempList(r->head, NULL);
				tail = ret;
			}
		}
	}
	return ret;
}

/*
 * Function: intersect
 * Description: 交集
 */
Temp_tempList intersect(Temp_tempList left, Temp_tempList right)
{
	Temp_tempList ret = NULL;
	Temp_tempList tail = NULL;
	for (Temp_tempList r = left; r; r = r->tail) {
		if (has(right, r->head)) {
			if (ret) {
				tail->tail = Temp_TempList(r->head, NULL);
				tail = tail->tail;
			}
			else {
				ret = Temp_TempList(r->head, NULL);
				tail = ret;
			}
		}
	}
	return ret;
}

/*
 * Function: difference
 * Description: 差集
 */
Temp_tempList difference(Temp_tempList left, Temp_tempList right)
{
	Temp_tempList ret = NULL;
	Temp_tempList tail = NULL;
	for (Temp_tempList r = left; r; r = r->tail) {
		if (!has(right, r->head)) {
			if (ret) {
				tail->tail = Temp_TempList(r->head, NULL);
				tail = tail->tail;
			}
			else {
				ret = Temp_TempList(r->head, NULL);
				tail = ret;
			}
		}
	}
	return ret;
}

/*
 * Function: set_equal
 * Description: Set Equal
 */
bool set_equal(Temp_tempList left, Temp_tempList right)
{
	int lsize = 0, rsize = 0;
	for (Temp_tempList tl = left; tl; tl = tl->tail) {
		lsize++;
	}
	for (Temp_tempList tl = right; tl; tl = tl->tail) {
		rsize++;
	}
	if (lsize != rsize) return FALSE;
	for (Temp_tempList tl = right; tl; tl = tl->tail) {
		if (!has(left, tl->head)) return FALSE;
	}
	return TRUE;
}

/*
 * Function: inMoveList
 * Description: if live move is in move list
 */
bool inMoveList(Live_moveList mvlist, G_node src, G_node dst)
{
	for (Live_moveList list = mvlist; list; list = list->tail) {
		if (list->src == src && list->dst == dst) return TRUE;
	}
	return FALSE;
}

struct Live_graph Live_liveness(G_graph flow) {
	// TODO:
	struct Live_graph lg;
	lg.graph = G_Graph();
	G_nodeList flowNodes = G_nodes(flow);
#if _DEBUG_
	file = fopen("__DEBUG_.md", "a");
	// fprintf(file, "# liveness\n");
	fprintf(file, "## 0\n");
	fprintf(file, "| Node index | successor | Node info |\n");
	fprintf(file, "| ---: | :--- | :--- |\n");
	G_show(file, flowNodes, (void (*)(void *))printAssem);
	fprintf(file, "-------------------\n");
	fclose(file);
#endif
	// in[instruction<n>]
	G_table inTab = G_empty();
	// out[instruction<n>]
	G_table outTab = G_empty();
	// temp - node table
	TAB_table tmpTab = TAB_empty();
	{
		/* Add machine registers into conflict graph */
		Temp_tempList hardregs = hardregisters();
		for (Temp_tempList hreg = hardregs; hreg; hreg = hreg->tail) {
			G_node gn = G_Node(lg.graph, hreg->head);
			TAB_enter(tmpTab, hreg->head, gn);
			for (Temp_tempList pre = hardregs; pre != hreg; pre = pre->tail) {
				G_node prevn = TAB_look(tmpTab, pre->head);
				G_addEdge(gn, prevn);
			}
		}
	}
#if _DEBUG_
	file = fopen("__DEBUG_.md", "a");
	fprintf(file, "# liveness\n");
	fprintf(file, "## 1\n");
	fprintf(file, "| Node index | successor | Node info |\n");
	fprintf(file, "| ---: | :--- | :--- |\n");
	G_show(file, flowNodes, (void (*)(void *))printAssem);
	fprintf(file, "-------------------\n");
	fclose(file);
#endif
	G_nodeList stack = NULL;
	{

		for (G_nodeList ns = flowNodes; ns; ns= ns->tail) {
			// Push instruction node
			stack = G_NodeList(ns->head, stack);
			Temp_tempList *tt = (Temp_tempList *) checked_malloc(sizeof(Temp_tempList));
			*tt = NULL;
			G_enter(inTab, ns->head, tt);
			tt = (Temp_tempList *) checked_malloc(sizeof(Temp_tempList));
			*tt = NULL;
			G_enter(outTab, ns->head, tt);
		}

		/* Add temps into conflict graph */
		for (G_nodeList flows = flowNodes; flows; flows = flows->tail) {
			Temp_tempList srcs = FG_use(flows->head);
			for (Temp_tempList tl = srcs; tl; tl = tl->tail) {
				if (!TAB_look(tmpTab, tl->head)) {
					G_node gn = G_Node(lg.graph, tl->head);
					TAB_enter(tmpTab, tl->head, gn);
				}
			}
			Temp_tempList dsts = FG_def(flows->head);
			for (Temp_tempList tl = dsts; tl; tl = tl->tail) {
				if (!TAB_look(tmpTab, tl->head)) {
					G_node gn = G_Node(lg.graph, tl->head);
					TAB_enter(tmpTab, tl->head, gn);
				}
			}
		}

	}
#if _DEBUG_
	file = fopen("__DEBUG_.md", "a");
	// fprintf(file, "# liveness\n");
	fprintf(file, "## 2\n");
	fprintf(file, "| Node index | successor | Node info |\n");
	fprintf(file, "| ---: | :--- | :--- |\n");
	G_show(file, flowNodes, (void (*)(void *))printAssem);
	fprintf(file, "-------------------\n");
	fclose(file);
#endif

#if _DEBUG_
	int debug_cycle = 0;
	file = fopen("__DEBUG_G_.md", "a");
	fprintf(file, "# Graph Table\n");
	fclose(file);
#endif

	// liveness analysis
	bool update = TRUE;
	while (update) {
		update = FALSE;

#if _DEBUG_
		file = fopen("__DEBUG_G_.md", "a");
		fprintf(file, "## Cycle %4d\n", debug_cycle);
		fprintf(file, "| Key | value |\n");
		fprintf(file, "| :--: | :--: |\n");
		TAB_dump(inTab, (void (*)(void *, void *))dump_map); // TODO:
		fprintf(file, "-------------\n");
		fclose(file);
		debug_cycle++;
#endif

		for (G_nodeList cursor = stack; cursor; cursor = cursor->tail)
		{
			G_node cur = cursor->head;
			Temp_tempList intemps = *(Temp_tempList *) G_look(inTab, cur);
			Temp_tempList outemps = *(Temp_tempList *) G_look(outTab, cur);
			// new out templist
			// out[n] <- ∪ {in[s]}    s ∈ succ[n]
			Temp_tempList noutemps = NULL;
			G_nodeList succ = G_succ(cur);
			while (succ) {
				assert(G_inNodeList(succ->head, flowNodes));
				Temp_tempList succ_list = *(Temp_tempList *) G_look(inTab, succ->head);
				noutemps = aggregate(noutemps, succ_list);
				succ = succ->tail;
			}
			// new in templist
			// in[n] <- use[n] ∪ (out[n] - def[n])
			Temp_tempList nintemps = aggregate(FG_use(cur),
																 difference(noutemps, FG_def(cur)));
			// update = update || ! set_equal(intemps, nintemps);
			// update = update || ! set_equal(outemps, noutemps);
			if (!set_equal(intemps, nintemps) || !set_equal(outemps, noutemps)) {
				update = TRUE;
			}
			*(Temp_tempList *) G_look(inTab, cur) = nintemps;
			*(Temp_tempList *) G_look(outTab, cur) = noutemps;
		}
	}
	//conflict graph 
	Live_moveList mvlist = NULL;
	for (G_nodeList nl = flowNodes; nl; nl = nl->tail) {
		Temp_tempList intmps = * (Temp_tempList *) G_look(inTab, nl->head);
		Temp_tempList outmps = * (Temp_tempList *) G_look(outTab, nl->head);

		if (FG_isMove(nl->head)) {
			/*
			 * Move instruction
			 * add def and dst pair to Move List
			 * add edge between def and out live temps which is not among src
			 */
			Temp_tempList srcs = FG_use(nl->head);
			Temp_tempList dsts = FG_def(nl->head);
			for (Temp_tempList cdst = dsts; cdst; cdst = cdst->tail){
				G_node dst_node = TAB_look(tmpTab, cdst->head);
				// conflict between dest temps
				for (Temp_tempList ccdst = cdst->tail; ccdst; ccdst = ccdst->tail) {
					G_node ndst_node = TAB_look(tmpTab, ccdst->head);
					if (ndst_node != dst_node && !G_inNodeList(ndst_node, G_adj(dst_node)))
						G_addEdge(dst_node, ndst_node);
				}

				// do not add conflict between src and dst
				// add move instruction's src and dst to LiveMoveList
				for (Temp_tempList csrc = srcs; csrc; csrc = csrc->tail){
					G_node src_node = TAB_look(tmpTab, csrc->head);
					if (!inMoveList(mvlist, src_node, dst_node))
						mvlist = Live_MoveList(src_node, dst_node, mvlist);
				}

				// dst conflict with those out lived temps but not in use
				for (Temp_tempList ot = outmps; ot; ot = ot->tail) {
					if (!inTemplist(srcs, ot->head)) {
						G_node otnode = TAB_look(tmpTab, ot->head);
						if (!G_inNodeList(otnode, G_adj(dst_node)))
							G_addEdge(otnode, dst_node);
					}
				}

			}
		}
		else {
			/* 
			 * Non move instruction
			 * Add edge between in temps and out temps
			 */
			Temp_tempList uList = aggregate(intmps, outmps);
			for (Temp_tempList it = uList; it; it = it->tail)
			{
				G_node itnode = TAB_look(tmpTab, it->head);

				for (Temp_tempList itt = uList->tail; itt; itt = itt -> tail) {
					G_node ittnode = TAB_look(tmpTab, itt->head);
					if (itnode != ittnode && !G_inNodeList(ittnode, G_adj(itnode)))
						G_addEdge(itnode, ittnode);
				}

			}
		}
	}
	lg.moves = mvlist;
	return lg;
}

#if _DEBUG_
void Live_mdump(FILE *out, Live_moveList mvList)
{
	for (Live_moveList cur = mvList; cur; cur = cur->tail) {
		Live_mprint(cur->src, cur->dst);
		fprintf(out, "\n");
	}
}

void Live_mprint(G_node src, G_node dst)
{
	if (inTemplist(hardregisters(), G_nodeInfo(src))) {
		string s = Temp_look(F_tempMap, G_nodeInfo(src));
		fprintf(file, "| %s |", s);
	}
	else {
		fprintf(file, "| t<%d> |", Temp_int(G_nodeInfo(src)));
	}
	if (inTemplist(hardregisters(), G_nodeInfo(dst))) {
		string s = Temp_look(F_tempMap, G_nodeInfo(dst));
		fprintf(file, " %s |", s);
	}
	else {
		fprintf(file, " t<%d> |", Temp_int(G_nodeInfo(dst)));
	}
}
#endif