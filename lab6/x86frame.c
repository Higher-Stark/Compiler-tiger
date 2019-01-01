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
Temp_label framesizeLabel = NULL;

// ------------ x86 64 Register ---------------------------

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
	framesizeLabel = Temp_namedlabel("L14_framesize");
	specialregs = Temp_empty();
	argregs = Temp_empty();
	calleesaves = Temp_empty();
	callersaves = Temp_empty();
	rax = Temp_newtemp();
	Temp_enter(specialregs, rax, "%rax");
	rcx = Temp_newtemp();
	Temp_enter(argregs, rcx, "%rcx");
	rdx = Temp_newtemp();
	Temp_enter(argregs, rdx, "%rdx");
	rbx = Temp_newtemp();
	Temp_enter(calleesaves, rbx, "%rbx");
	rsi = Temp_newtemp();
	Temp_enter(argregs, rsi, "%rsi");
	rdi = Temp_newtemp();
	Temp_enter(argregs, rdi, "%rdi");
	rsp = Temp_newtemp();
	Temp_enter(specialregs, rsp, "%rsp");
	rbp = Temp_newtemp();
	Temp_enter(calleesaves, rbp, "%rbp");
	r8 = Temp_newtemp();
	Temp_enter(argregs, r8, "%r8");
	r9 = Temp_newtemp();
	Temp_enter(argregs, r9, "%r9");
	r10 = Temp_newtemp();
	Temp_enter(callersaves, r10, "%r10");
	r11 = Temp_newtemp();
	Temp_enter(callersaves, r11, "%r11");
	r12 = Temp_newtemp();
	Temp_enter(calleesaves, r12, "%r12");
	r13 = Temp_newtemp();
	Temp_enter(calleesaves, r13, "%r13");
	r14 = Temp_newtemp();
	Temp_enter(calleesaves, r14, "%r14");
	r15 = Temp_newtemp();
	Temp_enter(calleesaves, r15, "%r15");
}

Temp_map F_registerMap(void)
{
	static Temp_map map = NULL;
	if (map) return map;
	map = Temp_empty();
	map = Temp_layerMap(map, specialregs);
	map = Temp_layerMap(map, argregs);
	map = Temp_layerMap(map, calleesaves);
	map = Temp_layerMap(map, callersaves);
	return map;
}

string F_literal(int i)
{
	switch(i) {
		case 0: return "none";
		case 1: return "%rax";
		case 2: return "%rcx";
		case 3: return "%rdx";
		case 4: return "%rbx";
		case 5: return "%rsi";
		case 6: return "%rdi";
		case 7: return "%rsp";
		case 8: return "%rbp";
		case 9: return "%r8";
		case 10: return "%r9";
		case 11: return "%r10";
		case 12: return "%r11";
		case 13: return "%r12";
		case 14: return "%r13";
		case 15: return "%r14";
		case 16: return "%r15";
	}
	assert(0);
}

Temp_tempList hardregisters()
{
	static Temp_tempList list = NULL;
	if (list) return list;
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

Temp_tempList callerSaves()
{
	static Temp_tempList callerSaveRegs = NULL;
	if (callerSaveRegs) return callerSaveRegs;
	callerSaveRegs = Temp_TempList(r10, Temp_TempList(r11, NULL));
	return callerSaveRegs;
}
Temp_tempList calleeSaves()
{
	static Temp_tempList calleeSaveRegs = NULL;
	if (calleeSaveRegs) return calleeSaveRegs;
	calleeSaveRegs = Temp_TempList(rbx, 
					Temp_TempList(rbp, 
						Temp_TempList(r12, 
							Temp_TempList(r13, 
								Temp_TempList(r14, 
									Temp_TempList(r15, NULL))))));
	return calleeSaveRegs;
}

Temp_tempList F_argregs()
{
	static Temp_tempList arglist = NULL;
	if (arglist) return arglist;
	arglist = Temp_TempList(rdi, 
							Temp_TempList(rsi, 
								Temp_TempList(rdx, 
									Temp_TempList(rcx, 
										Temp_TempList(r8, 
											Temp_TempList(r9, NULL))))));
	return arglist;
}

/*
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

Temp_temp F_RDX(void)
{
	return rdx;
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
		case 1: return "%rdi";
		case 2: return "%rsi";
		case 3: return "%rdx";
		case 4: return "%rcx";
		case 5: return "%r8";
		case 6: return "%r9";
	}
	assert(0);
}

// ------------------------ x86 64 Frame ------------------------

// frame contains a Symbol indicates function name 
// and a list of argument and local  variable
struct F_frame_ {
	Temp_label name;
	long frameSize;
	// formals escape list
	U_boolList formalEscapeList;
	// formals access list
	F_accessList formals;
	// local variables
	F_accessList locals;
	// amount of outgoings
	int outCnt;

	// Temp_tempList temps;
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

/*
 * Create a frame named name and has a list of formals
 * | ... |
 * | arg[7] |
 * | static link |
 * | ret addr    |
 * ---------------
 * | callee      |
 * | saved       |
 * | registers   | <- frame pointer
 * ---------------
 * |  caller     |
 * | saved       |
 * | registers   |
 * ---------------
 * | escaped     |
 * | formals     |
 * ---------------
 * | locals      |
 * |  ...        |
 * ---------------
 * | outgoing    |
 * | args        |
 * | static link | <- stack pointer
 * ---------------
 */
F_frame F_newFrame(Temp_label name, U_boolList formals)
{
	F_frame ret = (F_frame) checked_malloc(sizeof (struct F_frame_));
	ret->name = name;
	// simply assume there will be a function call
	// in function body, one word size for static link
	// another word size for return address
	// for static link
	ret->frameSize = F_wordSize * 2;
	ret->outCnt = 1;
	ret->formalEscapeList = formals;
	// TODO: modify procEntryExit1 to meet arg location
	for (Temp_tempList tl = callerSaves(); tl; tl = tl->tail) {
		F_allocLocal(ret, TRUE);
	}
	for (Temp_tempList tl = F_argregs(); tl; tl = tl->tail ) {
		F_allocLocal(ret, TRUE);
	}
	U_boolList cursor = formals;
	F_accessList list = NULL;
	F_accessList tail = list;
	int fmlcnt = 1;

	// static link
	list = F_newAccessList(F_inFrame(F_wordSize * 7), NULL);
	tail = list;
	cursor = cursor->tail;
	{
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
				// the seventh parameter is 2 work size above frame pointer
				next = F_inFrame(F_wordSize * (fmlcnt + 1));
			}
			cursor = cursor->tail;
			fmlcnt++;
			// update access list
			tail->tail = F_newAccessList(next, NULL);
			tail = tail->tail;

		}
	}
	ret->formals = list;
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
	F_access ret = NULL;
	if (escape) {
		f->frameSize += F_wordSize;
		F_accessList list = f->locals;
		int i = 1;
		while (list) {
			i++;
			list = list->tail;
		}
		ret = F_inFrame(-F_wordSize * i);
		f->locals = F_newAccessList(ret, f->locals);
	}
	else {
		ret = F_inReg(Temp_newtemp());
	}
	return ret;
}

/*
 * allocate space on stack for outgoing parameters.
 * the space equals the function call with most parameters
 */ 
void F_allocOutgoing(F_frame f, int outCnt)
{
	if (outCnt > f->outCnt - 1) {
		f->frameSize += F_wordSize * (outCnt + 1 - f->outCnt);
		f->outCnt = outCnt + 1;
	}
}

F_accessList F_formals (F_frame f)
{
	return f->formals;
}

/*
 * calculate the access address
 */
T_exp F_Exp(F_access acc, T_exp framePtr)
{
	switch(acc->kind) {
		case inFrame: {
			if (framePtr->kind == T_TEMP && framePtr->u.TEMP == rbp) {
				return T_Mem(
					T_Binop(T_plus, 
					T_Const(acc->u.offset), 
					T_Binop(T_plus, T_Name(framesizeLabel) ,T_Temp(rsp))));
			} 
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
	return T_Call(T_Name(Temp_namedlabel(s)), T_ExpList(T_Temp(F_FP()), args));
}

T_stm F_procEntryExit1(F_frame frame, T_exp body)
{
	// Save callee-saved registers
	T_stm prologue = NULL;
	// Move escaped parameters in first 6 parameters to stack
	int idx = 1;
	Temp_tempList mregs = F_argregs();
	int cnt = 9;
	for (U_boolList bl = frame->formalEscapeList->tail; bl; bl = bl->tail) {
		if (bl->head && idx < 6) {
			T_stm s = T_Move(
				T_Mem(
					T_Binop(T_plus, T_Const(- F_wordSize * cnt), 
					T_Binop(T_plus, T_Name(framesizeLabel), T_Temp(F_SP())))), T_Temp(r(idx)));
			cnt++;
			if (prologue) prologue = T_Seq(s, prologue);
			else prologue = s;
		}
		idx++;
	}

	T_stm ss = T_Move(T_Temp(F_RV()), body);
	if (prologue) return T_Seq(prologue, ss);
	else return ss;
}

static Temp_tempList returnSink = NULL;

AS_instrList F_procEntryExit2(AS_instrList body)
{
	if (!returnSink) returnSink = Temp_TempList(
		F_RV(), Temp_TempList(F_SP(), NULL));
	return AS_splice(body, 
	AS_InstrList(AS_Oper("", NULL, returnSink, NULL), NULL));
}

/*
 * Add prologue and epilogue.
 * Prologue: allocate frame space
 * Epilogue: deallocate frame space and return and set frame size
 */
AS_proc F_procEntryExit3(F_frame frame, AS_instrList body)
{
	char pro[255];
	const string prosave = "pushq\t%rbx\npushq\t%rbp\npushq\t%r12\npushq\t%r13\npushq\t%r14\npushq\t%r15\n";
	const string epirestore = "popq\t%r15\npopq\t%r14\npopq\t%r13\npopq\t%r12\npopq\t%rbp\npopq\t%rbx\n";
	sprintf(pro, "\t.%s=%ld\n%ssubq\t$.%s, %%rsp\n",
	Temp_labelstring(framesizeLabel), frame->frameSize, prosave, Temp_labelstring(framesizeLabel));
	char epi[255];
	sprintf(epi, "addq\t$.%s, %%rsp\n%sret\n",
					Temp_labelstring(framesizeLabel), epirestore);
	return AS_Proc(String(pro), body, String(epi));
}

