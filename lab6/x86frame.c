#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/

const int F_wordSize = 8;

// frame contains a Symbol indicates function name 
// and a list of argument and local  variable
struct F_frame_ {
	Temp_label name;
	F_accessList formals;
	F_accessList locals;

	Temp_tempList temps;
};

//varibales
struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

F_accessList F_newAccessList(F_access head, F_accessList tail)
{
	F_accessList ret = (F_accessList) checked_malloc(sizeof(struct F_accessList_));
	ret->head = head;
	ret->tail = tail;
	return ret;
}

F_frag F_StringFrag(Temp_label label, string str) {   
	F_frag res = (F_frag) checked_malloc(sizeof(struct F_frag_));
	res->kind = F_stringFrag;
	res->u.stringg.label = label;
	res->u.stringg.str = str;
	fl = appendFrag(fl, res);
	return res;
}
                                                      
F_frag F_ProcFrag(T_stm body, F_frame frame) {        
	F_frag res = (F_frag) checked_malloc(sizeof(struct F_frag_));
	res->kind = F_procFrag;
	res->u.proc.body = body;
	res->u.proc.frame = frame;
	fl = appendFrag(fl, res);
	return res;
}

static F_fragList appendFrag(F_fragList l, F_frag f)
{
	F_fragList cur = l;
	if (cur) {
		while (cur->tail) {
			cur = cur->tail;
		}
		cur->tail = F_FragList(f, NULL);
	}
	else {
		l = F_FragList(f, NULL);
	}
	return l;
}
                                                      
F_fragList F_FragList(F_frag head, F_fragList tail) {
	F_fragList ret = (F_fragList) checked_malloc(sizeof(struct F_fragList_));
	ret->head = head;
	ret->tail = tail;
	return ret;
}

F_fragList F_getResult(void)
{
	return fl;
}

Temp_temp rax = NULL, rcx = NULL, 
					rdx = NULL, rbx = NULL,
					rsi = NULL, rdi = NULL,
					rsp = NULL, rbp = NULL,
					r8  = NULL, r9  = NULL,
					r10 = NULL, r11 = NULL,
					r12 = NULL, r13 = NULL,
					r14 = NULL, r15 = NULL;

void init_tempMap()
{
	// F_tempMap = Temp_empty();
	rax = Temp_newtemp();
	Temp_enter(F_tempMap, rax, "%%rax");
	rcx = Temp_newtemp();
	Temp_enter(F_tempMap, rcx, "%%rcx");
	rdx = Temp_newtemp();
	Temp_enter(F_tempMap, rdx, "%%rdx");
	rbx = Temp_newtemp();
	Temp_enter(F_tempMap, rbx, "%%rbx");
	rsi = Temp_newtemp();
	Temp_enter(F_tempMap, rsi, "%%rsi");
	rdi = Temp_newtemp();
	Temp_enter(F_tempMap, rdi, "%%rdi");
	rsp = Temp_newtemp();
	Temp_enter(F_tempMap, rsp, "%%rsp");
	rbp = Temp_newtemp();
	Temp_enter(F_tempMap, rbp, "%%rbp");
	r8 = Temp_newtemp();
	Temp_enter(F_tempMap, r8, "%%r8");
	r9 = Temp_newtemp();
	Temp_enter(F_tempMap, r9, "%%r9");
	r10 = Temp_newtemp();
	Temp_enter(F_tempMap, r10, "%%r10");
	r11 = Temp_newtemp();
	Temp_enter(F_tempMap, r11, "%%r11");
	r12 = Temp_newtemp();
	Temp_enter(F_tempMap, r12, "%%r12");
	r13 = Temp_newtemp();
	Temp_enter(F_tempMap, r13, "%%r13");
	r14 = Temp_newtemp();
	Temp_enter(F_tempMap, r14, "%%r14");
	r15 = Temp_newtemp();
	Temp_enter(F_tempMap, r15, "%%r15");
}

// create a new Frame with label name and formals
// TODO: x86 only allow at most 6 formals in register
F_frame F_newFrame(Temp_label name, U_boolList formals)
{
	F_frame ret = (F_frame) checked_malloc(sizeof (struct F_frame_));
	ret->name = name;
	U_boolList cursor = formals;
	F_accessList list = NULL;
	F_accessList tail = list;
	Temp_tempList tmplist = NULL;
	Temp_tempList tmptail = NULL;
	int fmlcnt = 0;
	while (cursor) {
		F_accessList newtail = (F_accessList) checked_malloc(sizeof(struct F_accessList_));
		F_access next = (F_access) checked_malloc(sizeof(struct F_access_));
		if (cursor->head) {
			next->kind = inFrame;
			next->u.offset = F_wordSize * fmlcnt;
			fmlcnt += 1;
		}
		else {
			next->kind = inReg;
			next->u.reg = Temp_newtemp();
			if (tmptail) {
				tmptail->tail = Temp_TempList(next->u.reg, NULL);
				tmptail = tmptail->tail;
			}
			else {
				tmplist = Temp_TempList(next->u.reg, NULL);
				tmptail = tmplist;
			}
		}
		newtail->head = next;
		newtail->tail = NULL;
		if (tail) {
			tail->tail = newtail;
			tail = tail->tail;
		}
		else {
			list = newtail;
			tail = newtail;
		}
		cursor = cursor->tail;
	}
	ret->formals = list;
	ret->locals = NULL;
	ret->temps = tmplist;
	return ret;
}

// get name of a frame
Temp_label F_name (F_frame f)
{
	return f->name;
}

// allocate a new local variable in the frame
F_access F_allocLocal (F_frame f, bool escape)
{
	F_access ret = (F_access) checked_malloc(sizeof(struct F_access_));
	if (escape) {
		ret->kind = inFrame;
		F_accessList list = f->locals;
		int i = 0;
		while (list) {
			i++;
			list = list->tail;
		}
		ret->u.offset = -F_wordSize * i - F_wordSize;
		f->locals = F_newAccessList(ret, f->locals);
		/*
		 * NO NEED !
		// allocate a space in frame for variable
		f->formals = U_BoolList(escape, f->formals);
		 */
	}
	else {
		ret->kind = inReg;
		Temp_temp newtmp = Temp_newtemp();
		ret->u.reg = newtmp;
		f->temps = Temp_TempList(newtmp, f->temps);
	}
	return ret;
}

F_accessList F_formals (F_frame f)
{
	return f->formals;
}

/*
 * TODO:
 * return frame pointer
 */
Temp_temp F_FP(void)
{
	return rbp;
}

/*
 * TODO:
 * return the location where return value is to be stored
 */
Temp_temp F_RV(void)
{
	return rax;
}

/*
 * calculate the access address
 */
T_exp F_Exp(F_access acc, T_exp framePtr)
{
	switch(acc->kind) {
		case inFrame: {
			return T_Mem(T_Binop(T_plus, framePtr, T_Const(acc->u.offset)));
		}
		case inReg: {
			return T_Temp(acc->u.reg);
		}
	}
	assert(0);
}

F_access F_offset(F_access acc, const int offset)
{
	if (acc->kind != inFrame) {
		// inFrame expected
		assert(0);
	}
	F_access newacc = (F_access) checked_malloc(sizeof(struct F_access_));
	newacc->kind = inFrame;
	newacc->u.offset = acc->u.offset - offset;
	return newacc;
}

T_exp F_externalCall(string s, T_expList args) {
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm)
{
	// TODO:
	return stm;
}