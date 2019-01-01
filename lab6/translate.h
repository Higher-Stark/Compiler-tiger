#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;

typedef struct Tr_expList_ *Tr_expList;

struct Tr_expList_ {
	Tr_exp head;
	Tr_expList tail;
};

typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;

struct Tr_accessList_ {
	Tr_access head;
	Tr_accessList tail;	
};

typedef struct Tr_level_ *Tr_level;

typedef struct Tr_field_ *Tr_field;

typedef struct Tr_fieldList_ *Tr_fieldList;

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail);

Tr_expList Tr_splice(Tr_expList head, Tr_expList tail);

Tr_expList Tr_append(Tr_expList head, Tr_exp e);

Tr_field Tr_Field(int order, Tr_exp exp);

Tr_fieldList Tr_FieldList(Tr_field head, Tr_fieldList tail);

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

Tr_accessList Tr_nextAccessList(Tr_accessList i);

Tr_level Tr_outermost(void);

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);

Tr_access Tr_allocLocal(Tr_level level, bool escape);

Tr_exp Tr_noop();

Tr_exp Tr_simpleVar(Tr_access, Tr_level);

Tr_exp Tr_fieldVar(Tr_exp ex, const int offset);

Tr_exp Tr_subscriptVar(Tr_exp ex, Tr_exp offset);

Tr_exp Tr_opExp(A_oper oper, Tr_exp left, Tr_exp right);

Tr_exp Tr_strcmpExp(A_oper oper, Tr_exp left, Tr_exp right);

Tr_exp Tr_nilExp();

Tr_exp Tr_intExp(int d);

string escapestr(string s);

Tr_exp Tr_strExp(string s);

Tr_exp Tr_ifExp(Tr_exp testt, Tr_exp thenn, Tr_exp elsee);

Tr_exp Tr_recordAlloc(int cnt, Tr_fieldList fields);

Tr_exp Tr_arrayAlloc(Tr_exp n, Tr_exp init);

Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Temp_label done);

Tr_exp Tr_forExp(Tr_access loopvar, Tr_exp low, Tr_exp high, Tr_exp body, Temp_label done);

Tr_exp Tr_breakExp(Temp_label done);

Tr_exp Tr_callExp(Tr_level callerlevel, Tr_level calleelevel, Temp_label name, Tr_expList explist);

Tr_exp Tr_letExp(Tr_expList decs, Tr_exp body);

Tr_exp Tr_seqExp(Tr_exp exp1, Tr_exp exp2);

Tr_exp Tr_assignExp(Tr_exp acc, Tr_exp exp);

Tr_exp Tr_varDec(Tr_access acc, Tr_exp init);

int Tr_funcDec(Tr_level l, Tr_exp body);

F_fragList Tr_getResult(void);

int Tr_ProcFrag(Tr_exp body, Tr_level l);
#endif
