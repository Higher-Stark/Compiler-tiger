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
const int F_reg_amount = 16;

// frame contains a Symbol indicates function name 
// and a list of argument and local  variable
struct F_frame_ {
	Temp_label name;
	long frameSize;
	U_boolList formalEscapeList;
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

Temp_map specialregs = NULL;
Temp_map argregs = NULL;
Temp_map calleesaves = NULL;
Temp_map callersaves = NULL;

void init_tempMap()
{
	specialregs = Temp_empty();
	argregs = Temp_empty();
	calleesaves = Temp_empty();
	callersaves = Temp_empty();
	rax = Temp_newtemp();
	Temp_enter(specialregs, rax, "%%rax");
	rcx = Temp_newtemp();
	Temp_enter(argregs, rcx, "%%rcx");
	rdx = Temp_newtemp();
	Temp_enter(argregs, rdx, "%%rdx");
	rbx = Temp_newtemp();
	Temp_enter(calleesaves, rbx, "%%rbx");
	rsi = Temp_newtemp();
	Temp_enter(argregs, rsi, "%%rsi");
	rdi = Temp_newtemp();
	Temp_enter(argregs, rdi, "%%rdi");
	rsp = Temp_newtemp();
	Temp_enter(specialregs, rsp, "%%rsp");
	rbp = Temp_newtemp();
	Temp_enter(calleesaves, rbp, "%%rbp");
	r8 = Temp_newtemp();
	Temp_enter(argregs, r8, "%%r8");
	r9 = Temp_newtemp();
	Temp_enter(argregs, r9, "%%r9");
	r10 = Temp_newtemp();
	Temp_enter(callersaves, r10, "%%r10");
	r11 = Temp_newtemp();
	Temp_enter(callersaves, r11, "%%r11");
	r12 = Temp_newtemp();
	Temp_enter(calleesaves, r12, "%%r12");
	r13 = Temp_newtemp();
	Temp_enter(calleesaves, r13, "%%r13");
	r14 = Temp_newtemp();
	Temp_enter(calleesaves, r14, "%%r14");
	r15 = Temp_newtemp();
	Temp_enter(calleesaves, r15, "%%r15");
}

Temp_map F_registerMap(void)
{
	static Temp_map map = NULL;
	if (!map) return map;
	map = Temp_empty();
	map = Temp_layerMap(map, specialregs);
	map = Temp_layerMap(map, argregs);
	map = Temp_layerMap(map, calleesaves);
	map = Temp_layerMap(map, callersaves);
	return map;
}

Temp_tempList hardregisters()
{
	static Temp_tempList list = NULL;
	if (!list) return list;
	if (rax && rcx && rdx && rbx && 
			rsi && rdi && rsp && rbp && 
			r8  && r9  && r10 && r11 && 
			r12 && r13 && r14 && r15) {
		list = Temp_TempList(rax, 
					 	Temp_TempList(rcx, 
						Temp_TempList(rdx, 
						Temp_TempList(rbx, 
						Temp_TempList(rsi, 
						Temp_TempList(rdi, 
						Temp_TempList(rsp, 
						Temp_TempList(rbp, 
						Temp_TempList(r8, 
						Temp_TempList(r9, 
						Temp_TempList(r10, 
						Temp_TempList(r11, 
						Temp_TempList(r12, 
						Temp_TempList(r13, 
						Temp_TempList(r14, 
						Temp_TempList(r15, NULL)
						)))))))))))))));
	}
}

Temp_temp r(int i)
{
	switch(i) {
		case 1: return rdi;
		case 2: return rsi;
		case 3: return rdx;
		case 4: return rcx;
		case 5: return r8;
		case 6: return r9;
	}
	assert(0);
}

string name_r(int i) {
	switch(i) {
		case 1: return "%%rdi";
		case 2: return "%%rsi";
		case 3: return "%%rdx";
		case 4: return "%%rcx";
		case 5: return "%%8";
		case 6: return "%%r9";
	}
	assert(0);
}

F_access F_inFrame(int offset) 
{
	F_access acc = (F_access) checked_malloc(sizeof(struct F_access_));
	acc->kind = inFrame;
	acc->u.offset = offset;
	return acc;
}

F_access F_inReg(Temp_temp reg)
{
	F_access acc = (F_access) checked_malloc(sizeof(struct F_access_));
	acc->kind = inReg;
	acc->u.reg = reg;
	return acc;
}

// create a new Frame with label name and formals
// TODO: x86 only allow at most 6 formals in register
F_frame F_newFrame(Temp_label name, U_boolList formals)
{
	F_frame ret = (F_frame) checked_malloc(sizeof (struct F_frame_));
	ret->name = name;
	ret->locals = NULL;
	ret->frameSize = 0;
	ret->formalEscapeList = formals;
	U_boolList cursor = formals;
	F_accessList list = NULL;
	F_accessList tail = list;
	Temp_tempList tmplist = NULL;
	Temp_tempList tmptail = NULL;
	int fmlcnt = 1;
	// int reg_formal = 0;

	{
		// static link
		list = F_newAccessList(F_inFrame(F_wordSize * 2), NULL);
		tail = list;
		cursor = cursor->tail;
		while (cursor) {
			F_access next = NULL;
			// fist 6 parameters
			if (fmlcnt <= 6) {
				if (cursor->head) {
					next = F_allocLocal(ret, TRUE);
				}
				else {
					next = F_inReg(r(fmlcnt));
				}
			}
			// more than 6 parameters
			else {
				next = F_inFrame(F_wordSize * (fmlcnt - 4));
			}
			cursor = cursor->tail;
			fmlcnt++;
			// update access list
			tail->tail = F_newAccessList(next, NULL);
			tail = tail->tail;

			// update templist
			if (next->kind == inReg) {
				if (tmptail) {
					tmptail->tail = Temp_TempList(next->u.reg, NULL);
					tmptail = tmptail->tail;
				}
				else {
					tmplist = Temp_TempList(next->u.reg, NULL);
					tmptail = tmplist;
				}
			}

		}
	}
	ret->formals = list;
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
		f->frameSize += F_wordSize;
		ret->kind = inFrame;
		F_accessList list = f->locals;
		int i = 0;
		while (list) {
			i++;
			list = list->tail;
		}
		ret->u.offset = -F_wordSize * i;
		f->locals = F_newAccessList(ret, f->locals);
	}
	else {
		ret = F_inReg(Temp_newtemp());
		// f->temps = Temp_TempList(ret->u.reg, f->temps);
		Temp_tempList tail = f->temps;
		while (tail && tail->tail) {
			tail = tail->tail;
		}
		if (tail) {
			tail->tail = Temp_TempList(ret->u.reg, NULL);
		}
		else {
			f->temps = Temp_TempList(ret->u.reg, NULL);
		}
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

Temp_temp F_SP(void)
{
	return rsp;
}

/*
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

int F_inFrameOffset(F_access acc)
{
	assert(acc->kind == inFrame);
	return acc->u.offset;
}

T_exp F_externalCall(string s, T_expList args) {
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm)
{
	U_boolList bl = frame->formalEscapeList;
	bl = bl->tail;
	int idx = 0;
	Temp_tempList mregs = calleeSaves();
	T_stm epilogue = NULL;
	while (bl && mregs) {
		if (bl->head && idx < 6) {
			T_stm s = T_Move(
								 T_Mem(
									T_Binop(T_plus, 
									 T_Const(F_wordSize * idx), T_Temp(F_FP()))), 
								 T_Temp(mregs->head));
			if (epilogue) epilogue = T_Seq(epilogue, s);
			else epilogue = s;
		}
		bl = bl->tail;
		mregs = mregs->tail;
		idx++;
	}

	// save callee-saved register
	Temp_tempList saves = calleeSaves();
	while (saves) {
		F_access acc = F_allocLocal(frame, TRUE);
		T_stm s = T_Move(F_Exp(acc, T_Temp(F_FP())), T_Temp(saves->head));
		if (epilogue)
			epilogue = T_Seq(epilogue, s);
		else
			epilogue = s;
		saves = saves->tail;
	}
	return T_Seq(epilogue, stm);
}

static Temp_tempList returnSink = NULL;

Temp_tempList callerSaves()
{
	return Temp_TempList(r10, Temp_TempList(r11, NULL));
}
Temp_tempList calleeSaves()
{
	return Temp_TempList(rbx, 
					Temp_TempList(rbp, 
						Temp_TempList(r12, 
							Temp_TempList(r13, 
								Temp_TempList(r14, 
									Temp_TempList(r15, NULL))))));
}
AS_instrList F_procEntryExit2(AS_instrList body)
{
	if (!returnSink) returnSink = Temp_TempList(
		rax, Temp_TempList(F_FP(), calleeSaves()));
	return AS_splice(body, 
	AS_InstrList(AS_Oper("", NULL, returnSink, NULL), NULL));
}

AS_proc F_procEntryExit3(F_frame frame, AS_instrList body)
{
	char buf[100];
	sprintf(buf, "PROCEDURE %s\n", S_name(frame->name));
	char epi[100];
	sprintf(epi, "%s\n\t.L14_framesize\t%ld\nEND\n",
					Temp_labelstring(Temp_newlabel()), frame->frameSize);
	return AS_Proc(String(buf), body, String(epi));
}

