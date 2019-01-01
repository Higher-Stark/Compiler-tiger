
/*Lab5: This header file is not complete. Please finish it with more definition.*/

#ifndef FRAME_H
#define FRAME_H

#include "tree.h"
#include "assem.h"

extern const int F_wordSize;
extern const int F_reg_amount;
extern Temp_label framesizeLabel;
typedef struct F_frame_ *F_frame;

typedef struct F_access_ *F_access;
typedef struct F_accessList_ *F_accessList;

struct F_accessList_ {F_access head; F_accessList tail;};

Temp_map F_tempMap;

void init_tempMap();

Temp_tempList hardregisters();

Temp_temp r(int i);

string name_r(int i);

F_frame F_newFrame(Temp_label name, U_boolList formals);

Temp_label F_name(F_frame f);

F_access F_allocLocal (F_frame f, bool escape);

void F_allocOutgoing(F_frame f, int outCnt);

F_accessList F_formals(F_frame f);

Temp_temp F_FP(void);

Temp_temp F_SP(void);

Temp_temp F_RV(void);

Temp_temp F_RDX(void);

Temp_map F_registerMap(void);

string F_literal(int i);

T_exp F_Exp(F_access acc, T_exp framePtr);

F_access F_offset(F_access acc, const int offset);

int F_inFrameOffset(F_access acc);

T_exp F_externalCall(string s, T_expList args);

Temp_tempList callerSaves();

Temp_tempList calleeSaves();

Temp_tempList F_argregs();

T_stm F_procEntryExit1(F_frame frame, T_exp body);

AS_instrList F_procEntryExit2(AS_instrList body);

AS_proc F_procEntryExit3(F_frame frame, AS_instrList body);

/* declaration for fragments */
typedef struct F_frag_ *F_frag;
struct F_frag_ {enum {F_stringFrag, F_procFrag} kind;
			union {
				struct {Temp_label label; string str;} stringg;
				struct {T_stm body; F_frame frame;} proc;
			} u;
};

F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);

typedef struct F_fragList_ *F_fragList;
struct F_fragList_ 
{
	F_frag head; 
	F_fragList tail;
};

static F_fragList fl = NULL;

F_fragList F_getResult(void);

static F_fragList appendFrag(F_fragList l, F_frag f);

F_fragList F_FragList(F_frag head, F_fragList tail);

#endif
