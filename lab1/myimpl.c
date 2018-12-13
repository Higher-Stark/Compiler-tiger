#include "prog1.h"
#include <stdio.h>
#include <string.h>

typedef struct table *Table_;
struct table {string id; int value; Table_ tail;};
Table_ Table(string id, int value, struct table *tail) {
	Table_ t = checked_malloc(sizeof(*t));
	t->id = id; t->value = value; t->tail = tail;
	return t;
}
Table_ update (string id, int value, Table_ tail) {
	Table_ t = Table(id, value, tail);
	return t;
}
int lookup(string id, Table_ t) {
	if (strcmp(id, t->id) != 0) return lookup(id, t->tail);
	else return t->value;
}

typedef struct IntAndTable *IntAndTable_;
struct IntAndTable {int i; Table_ t;};
IntAndTable_ IntAndTable(int v, Table_ t) {
	IntAndTable_ it = checked_malloc(sizeof(*it));
	it->i = v;
	it->t = t;
	return it;
}

int countExp(A_exp exp);
int countExpList(A_expList exps);
int maxargs(A_stm stm);

IntAndTable_ interpExp (A_exp exp, Table_ t);
Table_ interpStm (A_stm stm, Table_ t);
void interp (A_stm);


int countExp(A_exp exp) 
{
	int count = 0;
	A_exp it = exp;
	while (it->kind == A_eseqExp) {
		int tmp = maxargs(it->u.eseq.stm);
		count = tmp > count ? tmp : count;
		it = it->u.eseq.exp;
	}
	return count;
}

int countExpList(A_expList exps) 
{
	int count = 0;
	A_expList it = exps;
	if (it->kind == A_lastExpList) {
		count = countExp(it->u.last);
	}
	else {
		int tmp = countExp(it->u.pair.head);
		count = tmp > count ? tmp : count;
		tmp = countExpList(it->u.pair.tail);
		count = tmp > count ? tmp : count;
	}
	return count;
}

int maxargs(A_stm stm)
{
	int count = 0;
	if (stm->kind == A_compoundStm) {
		int count1 = maxargs(stm->u.compound.stm1);
		int count2 = maxargs(stm->u.compound.stm2);
		count = count1 > count2 ? count1 : count2;
	}
	else if (stm->kind == A_printStm) {
		A_expList list = stm->u.print.exps;
		while (list->kind != A_lastExpList) {
			count ++;
			list = list->u.pair.tail;
		}
		count ++;
		int tmp = countExpList(stm->u.print.exps);
		count = tmp > count ? tmp : count;
	}
	else if (stm->kind == A_assignStm) {
		int tmp = countExp(stm->u.assign.exp);
		count = tmp > count ? tmp : count;
	}
	return count;
}

IntAndTable_ interpExp(A_exp exp, Table_ t) 
{
	switch(exp->kind) {
		case A_idExp: {
			return IntAndTable(lookup(exp->u.id, t), t);
		}
		case A_numExp: {
			return IntAndTable(exp->u.num, t);
		}
		case A_opExp : {
			int left = interpExp(exp->u.op.left, t)->i;
			int right = interpExp(exp->u.op.right, t)->i;
			switch (exp->u.op.oper) {
				case A_plus: 
					return IntAndTable(left + right, t);
				case A_minus:
					return IntAndTable(left - right, t);
				case A_times: 
					return IntAndTable(left * right, t);
				case A_div:
					return IntAndTable(left / right, t);
				default: ;
			}
			return NULL;
		}
		case A_eseqExp: {
			Table_ new_t = interpStm(exp->u.eseq.stm, t);
			IntAndTable_ res = interpExp(exp->u.eseq.exp, new_t);
			return res;
		}
		default: ;
	}
	return NULL;
}

Table_ interpStm(A_stm stm, Table_ t)
{
	switch(stm->kind) {
		case A_compoundStm: {
			Table_ new_t = interpStm(stm->u.compound.stm1, t);
			new_t = interpStm(stm->u.compound.stm2, new_t);
			return new_t;
		}
		case A_assignStm: {
			IntAndTable_ ret = interpExp(stm->u.assign.exp, t);
			Table_ new_t = Table(stm->u.assign.id, ret->i, ret->t);
			return new_t;
		}
		case A_printStm: {
			A_expList exps = stm->u.print.exps;
			while (exps->kind != A_lastExpList) {
				IntAndTable_ res = interpExp(exps->u.pair.head, t);
				t = res->t;
				printf("%d ", res->i);
				exps = exps->u.pair.tail;
			}
			IntAndTable_ res = interpExp(exps->u.last, t);
			printf("%d\n", res->i);
			return res->t;
		}
		default: ;
	}
	return t;
}

void interp(A_stm stm)
{
	Table_ t = NULL;
	interpStm(stm, t);
}
