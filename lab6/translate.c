#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

//LAB5: you can modify anything you want.


static F_fragList fraglist;

struct Tr_access_ {
	Tr_level level;
	F_access access;
};


struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
};

struct Tr_field_ {
	int order;
	Tr_exp exp;
};

struct Tr_fieldList_ {
	Tr_field head;
	Tr_fieldList tail;
};

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};

Tr_field Tr_Field(int order, Tr_exp exp)
{
	Tr_field ret = (Tr_field) checked_malloc(sizeof(struct Tr_field_));
	ret->order = order;
	ret->exp = exp;
	return ret;
}

Tr_fieldList Tr_FieldList(Tr_field head, Tr_fieldList tail)
{
	Tr_fieldList ret = (Tr_fieldList) checked_malloc(sizeof(struct Tr_fieldList_));
	ret->head = head;
	ret->tail = tail;
	return ret;
}

Tr_exp Tr_Ex(T_exp ex)
{
	Tr_exp e = (Tr_exp) checked_malloc(sizeof(struct Tr_exp_));
	e->kind = Tr_ex;
	e->u.ex = ex;
	return e;
}

Tr_exp Tr_Nx(T_stm st)
{
	Tr_exp e = (Tr_exp) checked_malloc(sizeof(struct Tr_exp_));
	e->kind = Tr_nx;
	e->u.nx = st;
	return e;
}

Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm)
{
	Tr_exp e = (Tr_exp) checked_malloc(sizeof(struct Tr_exp_));
	e->kind = Tr_cx;
	e->u.cx.stm = stm;
	e->u.cx.trues = trues;
	e->u.cx.falses = falses;
	return e;
}

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail)
{
	Tr_expList el = (Tr_expList) checked_malloc(sizeof(struct Tr_expList_));
	el->head = head;
	el->tail = tail;
	return el;
}

static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

void doPatch(patchList tList, Temp_label label)
{
	for(; tList; tList = tList->tail)
		*(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second)
{
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

// return a new access list with head head and tail tail
Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail)
{
	Tr_accessList ret = (Tr_accessList) checked_malloc(sizeof(struct Tr_accessList_));
	ret->head = head;
	ret->tail = tail;
	return ret;
}

Tr_accessList Tr_nextAccessList(Tr_accessList i)
{
	return i->tail;
}

static Tr_level outermost = NULL;

Tr_level Tr_outermost(void)
{
	if (outermost) {
		return outermost;
	}
	return Tr_newLevel(NULL, Temp_newlabel(), NULL);
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
	Tr_level sublevel = (Tr_level) checked_malloc(sizeof(struct Tr_level_));
	sublevel->parent = parent;
	sublevel->frame = F_newFrame(name, U_BoolList(TRUE, formals));
	return sublevel;
}

// Encapsulate F_accessList
// Transform F_accessList to Tr_accessList
Tr_accessList Tr_formals(Tr_level level)
{
	F_accessList cursor = F_formals(level->frame);
	if (!cursor) return NULL;
	Tr_accessList ret = NULL;
	Tr_accessList tail = NULL;
	while (cursor) {
		Tr_access acc = (Tr_access) checked_malloc(sizeof(struct Tr_access_));
		acc->access = cursor->head;
		acc->level = level;
		Tr_accessList newtail = (Tr_accessList) checked_malloc(sizeof(struct Tr_accessList_));
		newtail->head = acc;
		if (tail) {
			tail->tail = newtail;
			tail = tail->tail;
		}
		else {
			ret = newtail;
			tail = newtail;
		}
		cursor = cursor->tail;
	}

	return ret;
}

// allocate a local variable in level frame
Tr_access Tr_allocLocal(Tr_level level, bool escape)
{
	Tr_access acc = (Tr_access) checked_malloc(sizeof(struct Tr_access_));
	acc->access = F_allocLocal(level->frame, escape);
	acc->level = level;
	return acc;
}

// transform an exp to exp
static T_exp unEx(Tr_exp e)
{
	switch (e->kind) {
		case Tr_ex: 
			return e->u.ex;
		case Tr_cx: {
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel(), f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Eseq(T_Move(T_Temp(r), T_Const(1)), 
					T_Eseq(e->u.cx.stm, 
					 T_Eseq(T_Label(f), 
					  T_Eseq(T_Move(T_Temp(r), T_Const(0)), 
					   T_Eseq(T_Label(t),
					   	T_Temp(r))))));
		}
		case Tr_nx: 
			return T_Eseq(e->u.nx, T_Const(0));
	}
	assert(0);
}

// transform an exp to statement
static T_stm unNx(Tr_exp e)
{
	switch(e->kind) {
		case Tr_ex: {
			return T_Exp(e->u.ex);
		}
		case Tr_cx: {
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel(), f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Seq(T_Move(T_Temp(r), T_Const(1)),
					T_Seq(e->u.cx.stm, 
					 T_Seq(T_Label(f), 
					  T_Seq(T_Move(T_Temp(r), T_Const(0)),
					   T_Seq(T_Label(t), 
					    T_Exp(T_Temp(r)))))));
		}
		case Tr_nx: {
			return e->u.nx;
		}
	}
	assert(0);
}

// transform an exp to a conditional statement
static struct Cx unCx(Tr_exp e)
{
	switch(e->kind) {
		case Tr_ex: {
			patchList trues = NULL, falses = NULL;
			T_stm s1 = T_Cjump(T_gt, e->u.ex, T_Const(0), NULL, NULL);
			trues = PatchList(&s1->u.CJUMP.true, NULL);
			falses = PatchList(&s1->u.CJUMP.false, NULL);
			Tr_exp c = Tr_Cx(trues, falses, s1);
			return c->u.cx;
		}
		case Tr_cx: {
			return e->u.cx;
		}
		case Tr_nx: {
			// nx are not expected to be transformed into cx
			assert(0);
		}
	}
	assert(0);
}

Tr_exp Tr_noop()
{
	return Tr_Ex(T_Const(0));
}

// translate a simple variable into a translated expression
Tr_exp Tr_simpleVar(Tr_access acc, Tr_level l)
{
	// TODO:
	T_exp ret = NULL;
	/*
	if (acc->level != l) {
		Tr_level cursor = l;
		ret = F_Exp(F_formals(l->frame)->head, T_Temp(F_FP()));
		while (cursor != acc->level) {
			ret = F_Exp(F_formals(l->frame)->head, ret);
			cursor = cursor->parent;
		}

	}
	*/

	Tr_level cursor = l;
	ret = T_Temp(F_FP());
	while (cursor != acc->level) {
		ret = F_Exp(F_formals(cursor->frame)->head, ret);
		cursor = cursor->parent;
	}
	ret = F_Exp(acc->access, ret);
	return Tr_Ex(ret);
}

Tr_exp Tr_fieldVar(Tr_exp ex, const int fieldIdx)
{
	return Tr_Ex(
			T_Mem(
			 T_Binop(T_plus, unEx(ex), T_Binop(
			  T_mul, T_Const(fieldIdx), T_Const(F_wordSize)))));
}

Tr_exp Tr_subscriptVar(Tr_exp ex, Tr_exp offset)
{
	return Tr_Ex(
			T_Mem(
			 T_Binop(
			  T_plus, unEx(ex), T_Binop(
			   T_mul, unEx(offset), T_Const(F_wordSize)))));
}

Tr_exp Tr_opExp(A_oper oper, Tr_exp left, Tr_exp right)
{
	switch(oper) {
		case A_plusOp: {
			return Tr_Ex(T_Binop(T_plus, unEx(left), unEx(right)));
		}
		case A_minusOp: {
			return Tr_Ex(T_Binop(T_minus, unEx(left), unEx(right)));
		}
		case A_timesOp: {
			return Tr_Ex(T_Binop(T_mul, unEx(left), unEx(right)));
		}
		case A_divideOp: {
			return Tr_Ex(T_Binop(T_div, unEx(left), unEx(right)));
		}
		case A_ltOp: {
			T_stm s = T_Cjump(T_lt, unEx(left), unEx(right), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_leOp: {
			T_stm s = T_Cjump(T_le, unEx(left), unEx(right), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_gtOp: {
			T_stm s = T_Cjump(T_gt, unEx(left), unEx(right), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_geOp: {
			T_stm s = T_Cjump(T_ge, unEx(left), unEx(right), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_eqOp: {
			T_stm s = T_Cjump(T_eq, unEx(left), unEx(right), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_neqOp: {
			T_stm s = T_Cjump(T_ne, unEx(left), unEx(right), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
	}
	assert(0);
}

Tr_exp Tr_strcmpExp(A_oper oper, Tr_exp left, Tr_exp right)
{
	T_exp res = F_externalCall("strcmp", T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
	switch(oper) {
		case A_ltOp: {
			T_stm s = T_Cjump(T_lt, res, T_Const(0), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_leOp: {
			T_stm s = T_Cjump(T_le, res, T_Const(0), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_gtOp: {
			T_stm s = T_Cjump(T_gt, res, T_Const(0), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_geOp: {
			T_stm s = T_Cjump(T_ge, res, T_Const(0), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_eqOp: {
			T_stm s = T_Cjump(T_eq, res, T_Const(0), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
		case A_neqOp: {
			T_stm s = T_Cjump(T_ne, res, T_Const(0), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
	}
}

Tr_exp Tr_nilExp() 
{
	return Tr_Ex(T_Const(0));
}

Tr_exp Tr_intExp(int d)
{
	return Tr_Ex(T_Const(d));
}

Tr_exp Tr_strExp(string s)
{
	Temp_label sl = Temp_newlabel();
	// TODO:
	F_frag str = F_StringFrag(sl, s);
	return Tr_Ex(T_Name(sl));
}

Tr_exp Tr_ifExp(Tr_exp testt, Tr_exp thenn, Tr_exp elsee)
{
	Temp_label t = Temp_newlabel(), f = Temp_newlabel(), joint = Temp_newlabel();
	
	if (testt->kind == Tr_ex) {
		struct Cx c = unCx(testt);
		testt = Tr_Cx(c.trues, c.falses, c.stm);
	}
	else if (testt->kind == Tr_nx) {
		assert(0);
	}

	doPatch(testt->u.cx.trues, t);
	doPatch(testt->u.cx.falses, f);

	if (elsee) {           // else statement exists
		if (thenn->kind == Tr_nx || elsee->kind == Tr_nx) { // non-valued if-then-else
			T_stm s2 = T_Seq(unCx(testt).stm, 
						T_Seq(T_Label(t), 
						 T_Seq(unNx(thenn), 
						  T_Seq(T_Jump(T_Name(joint), Temp_LabelList(joint, NULL)), 
						   T_Seq(T_Label(f), T_Seq(unNx(elsee), T_Label(joint)))))));
			return Tr_Nx(s2);
		}
		else {												// valued if-then-else
			Temp_temp r = Temp_newtemp();
			T_stm s2 = T_Seq(unCx(testt).stm, 
						T_Seq(T_Label(t), 
						 T_Seq(T_Move(T_Temp(r), unEx(thenn)), 
						  T_Seq(T_Jump(T_Name(joint), Temp_LabelList(joint, NULL)), 
						   T_Seq(T_Label(f), 
						    T_Seq(
							 T_Move(T_Temp(r), unEx(elsee)), 
							 T_Label(joint)))))));
			return Tr_Ex(T_Eseq(s2, T_Temp(r)));
		}
	}
	else {                  // else statment doesn't exists
		T_stm s2 = T_Seq(unCx(testt).stm, 
					T_Seq(T_Label(t), 
					 T_Seq(unNx(thenn), T_Label(f))));
		return Tr_Nx(s2);
	}
	assert(0);
}

/*
 * allocate heap space for record
 * fields is in reverse order comparing to record creation
 */
Tr_exp Tr_recordAlloc(int cnt, Tr_fieldList fields) 
{
	Temp_temp r = Temp_newtemp();
	Tr_fieldList f = fields;
	T_stm alloc = T_Move(T_Temp(r), 
	 F_externalCall("malloc", 
	  T_ExpList(
	   T_Binop(T_mul, T_Const(cnt), T_Const(F_wordSize)), NULL)));
	T_stm movs = NULL;
	while (f) {
		T_stm mov = T_Move(
					 T_Mem(T_Binop(T_plus, T_Temp(r), 
					  T_Binop(T_mul, T_Const(f->head->order), 
					   T_Const(F_wordSize)))), unEx(f->head->exp));
		if (!movs) movs = mov;
		else movs = T_Seq(mov, movs);
		f = f->tail;
	}
	return Tr_Ex(T_Eseq(T_Seq(alloc, movs), T_Temp(r)));
}

/*
 * allocate array space for array
 * @n : number of array elements
 * @init : initial value for each array element
 */
Tr_exp Tr_arrayAlloc(Tr_exp n, Tr_exp init)
{
	return Tr_Ex(F_externalCall(String("initArray"), 
			 T_ExpList(unEx(n), T_ExpList(unEx(init), NULL))));
}

/*
 * translate while into IR
 * @test: test statement of while loop
 * @body: while body
 * @done: end of while loop
 */
Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Temp_label done)
{
	struct Cx c = unCx(test);
	Tr_exp s1 = Tr_Cx(c.trues, c.falses, c.stm);
	Temp_label testl = Temp_newlabel();
	Temp_label bodyl = Temp_newlabel();
	doPatch(s1->u.cx.trues, bodyl);
	doPatch(s1->u.cx.falses, done);
	T_stm s2 = T_Seq(T_Label(testl), 
				T_Seq(unCx(s1).stm, 
				 T_Seq(T_Label(bodyl), 
				  T_Seq(unNx(body), 
				   T_Seq(
					T_Jump(
					 T_Name(testl), Temp_LabelList(testl, NULL)), 
					  T_Label(done))))));
	return Tr_Nx(s2);
}

/* 
 * translate for loop into IR
 * @loopvar: loop variable
 * @low: low bound of the loop variable
 * @high: high bound of the loop variable
 * @body: body of for loop
 * @done: end of the for loop
 */
Tr_exp Tr_forExp(Tr_access loopvar, Tr_exp low, Tr_exp high, Tr_exp body, Temp_label done)
{
	Temp_label loop = Temp_newlabel();
	Temp_label z = Temp_newlabel();
	Temp_label zz = Temp_newlabel();
	T_stm s1 = T_Cjump(T_le, unEx(low), unEx(high), z, done);
	T_stm s2 = T_Seq(T_Label(z),  
				T_Seq(T_Move(F_Exp(loopvar->access, T_Temp(F_FP())), unEx(low)), 
				 T_Seq(T_Cjump(T_gt, F_Exp(loopvar->access, T_Temp(F_FP())), unEx(high), done, zz), 
				  T_Seq(T_Label(zz), 
				   T_Seq(unNx(body), 
				    T_Seq(T_Cjump(T_eq, F_Exp(loopvar->access, T_Temp(F_FP())), unEx(high), done, loop), 
				     T_Seq(T_Label(loop), 
					  T_Seq(
					   T_Exp(
						T_Binop(T_plus, 
						 F_Exp(loopvar->access, T_Temp(F_FP())), T_Const(1))), 
					   T_Seq(unNx(body), 
					    T_Seq(
						 T_Cjump(T_lt, F_Exp(loopvar->access, T_Temp(F_FP())), unEx(high), loop, done), T_Label(done)))))))))));
	return Tr_Nx(T_Seq(s1, s2));
}

/*
 * translate break statement
 * @done: end of loop
 */
Tr_exp Tr_breakExp(Temp_label done)
{
	return Tr_Nx(T_Jump(T_Name(done), Temp_LabelList(done, NULL)));
}

T_expList argument(Tr_expList explist)
{
	T_expList ret = NULL;
	Tr_expList cursor = explist;
	while (cursor) {
		ret = T_ExpList(unEx(cursor->head), ret);
		cursor = cursor->tail;
	}
	return ret;
}

/*
 * translate function call
 * @callerlevel: level of caller function
 * @calleelevel: level of callee
 * @name: function name
 * @explist: expression list of argument
 */
Tr_exp Tr_callExp(Tr_level callerlevel, Tr_level calleelevel, Temp_label name, Tr_expList explist)
{
	Tr_level cur = callerlevel;
	T_exp link = T_Temp(F_FP());
	while (cur != calleelevel->parent) {
		link = F_Exp(F_formals(cur->frame)->head, link);
		cur = cur->parent;
	}
	return Tr_Ex(T_Call(T_Name(name), T_ExpList(link, argument(explist))));
}

/*
 * translate let expression
 * @decs: declarations of let expression
 * @body: body of let expression
 */
Tr_exp Tr_letExp(Tr_expList decs, Tr_exp body)
{
	T_stm el = NULL;
	Tr_expList cur = decs;
	while (cur) {
		if (el) {
			el = T_Seq(el, unNx(cur->head));
		}
		else {
			el = unNx(cur->head);
		}
		cur = cur->tail;
	}
	return Tr_Ex(T_Eseq(el, unEx(body)));
}

/*
 * translate sequence expression
 * @exp1: first expression in the sequence
 * @exp2: latter expression in the sequence
 */
Tr_exp Tr_seqExp(Tr_exp exp1, Tr_exp exp2)
{
	return Tr_Ex(T_Eseq(unNx(exp1), unEx(exp2)));
}

/*
 * translate assignment expression
 * @acc: access to left value to be assigned
 * @exp: value to assign
 */
Tr_exp Tr_assignExp(Tr_exp acc, Tr_exp exp)
{
	T_stm s1 = T_Move(unEx(acc), unEx(exp));
	return Tr_Nx(s1);
}

/*
 * translate variable declaration
 * @acc: access to the variable
 * @init: initial value for the variable
 */
Tr_exp Tr_varDec(Tr_access acc, Tr_exp init)
{
	T_stm s1 = T_Move(F_Exp(acc->access, T_Temp(F_FP())), unEx(init));
	return Tr_Nx(s1);
}

/*
 * translate function declaration
 * 
 * .function_label
 * <function prologue>
 * <function body>
 * <function epilogue>
 * 
 * @level: nested level of the function
 * @body: function body
 */
int Tr_funcDec(Tr_level l, Tr_exp body)
{
	T_stm bd = F_procEntryExit1(l->frame, unNx(body));
	F_frag f = F_ProcFrag(bd, l->frame);
	return 0;
}

/*
 * get fragment list head
 */
F_fragList Tr_getResult(void)
{
	return F_getResult();
}

/*
 * create a fragment for function
 * @body: function body expressions
 * @l: function level
 */
int Tr_ProcFrag(Tr_exp body, Tr_level l)
{
	F_frag fg = F_ProcFrag(unNx(body), l->frame);
	return 0;
}