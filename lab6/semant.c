#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "helper.h"
#include "translate.h"
#include "escape.h"

/*Lab5: Your implementation of lab5.*/

struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_ty actual_ty (Ty_ty ty)
{
	Ty_ty ret = ty;
	while (ret && ret->kind == Ty_name) {
		ret = ret->u.name.ty;
		if (ret == ty) break;
	}
	return ret;
}

int compatible(Ty_ty left, Ty_ty right)
{
	if (left == right) return TRUE;
	if (left->kind == Ty_array) {
		return left == right;
	}
	if (left->kind == Ty_record) {
		return right->kind == Ty_nil;
	}
	if (right->kind == Ty_record){
		return left->kind = Ty_nil;
	}
	return left->kind == right->kind;
}

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level l, Temp_label label)
{
	switch(v->kind) {
		case A_simpleVar: {
			// translate a simple variable
			E_enventry x = S_look(venv, get_simplevar_sym(v));
			if (x && x->kind == E_varEntry) {
				Tr_exp e = Tr_simpleVar(get_var_access(x), l);
				return expTy(e, actual_ty(x->u.var.ty));
			}
			else {
				EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
			}
			return expTy(Tr_nilExp(), Ty_Int());
		}
		case A_fieldVar: {
			// translate field variable in form of a.b.c
			struct expty varty = transVar(venv, tenv, get_fieldvar_var(v), l, label);
			if (varty.ty->kind != Ty_record) {
				EM_error(v->pos, "not a record type", v->u.simple);
				return expTy(Tr_nilExp(), varty.ty);
			}
			int fieldIdx = 0;
			for (Ty_fieldList list = get_record_fieldlist(varty); list; list = list->tail) {
				Ty_field head = list->head;
				if (head->name == get_fieldvar_sym(v)) {
					return expTy(Tr_fieldVar(varty.exp, fieldIdx), actual_ty(head->ty));
				}
				fieldIdx++;
			}
			EM_error(v->pos, "field %s doesn't exist", S_name(v->u.field.sym));
			return expTy(Tr_nilExp(), Ty_Int());
		}
		case A_subscriptVar: {
			// translate a subscript variable like a[i], a.b[j]
			struct expty varty = transVar(venv, tenv, v->u.subscript.var, l, label);
			struct expty indexty = transExp(venv, tenv, v->u.subscript.exp, l, label);
			if (varty.ty->kind != Ty_array) EM_error(v->pos, "array type required");
			else {
				if (indexty.ty->kind != Ty_int) {
					EM_error(v->u.subscript.exp->pos, "subscript must be int");
				}
				else {
					return expTy(Tr_subscriptVar(varty.exp, indexty.exp), actual_ty(varty.ty->u.array));
				}
			}
			return expTy(Tr_nilExp(), Ty_Int());
		}
	}
	assert(0);
	// return expTy(NULL, NULL);
}

struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level l ,Temp_label label)
{
	switch(a->kind) {
		case A_opExp: {
			A_oper oper = get_opexp_oper(a);
			struct expty left = transExp(venv, tenv, get_opexp_left(a), l, label);
			struct expty right = transExp(venv, tenv, get_opexp_right(a), l, label);
			// arithmatic expression
			if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp) {
				if (actual_ty(left.ty)->kind != Ty_int) EM_error(get_opexp_leftpos(a), "integer required");
				if (actual_ty(right.ty)->kind != Ty_int) EM_error(get_opexp_rightpos(a), "integer required");
				Tr_exp e = Tr_opExp(oper, left.exp, right.exp);
				return expTy(e, Ty_Int());
			}
			// comparing expression
			else if (oper == A_ltOp || oper == A_leOp || oper == A_gtOp || oper == A_geOp) {
				Ty_ty left_rootty = actual_ty(left.ty);
				if (left_rootty->kind != Ty_int && left_rootty->kind != Ty_string) EM_error(get_opexp_leftpos(a), "integer or string required");
				Ty_ty right_rootty = actual_ty(right.ty);
				if (right_rootty->kind != Ty_int && right_rootty->kind != Ty_string) EM_error(get_opexp_rightpos(a), "integer or string required");
				if (left_rootty->kind != right_rootty->kind) EM_error(get_opexp_rightpos(a), "same type required");
				Tr_exp e;
				if (left_rootty->kind != Ty_string) e = Tr_opExp(oper, left.exp, right.exp);
				else e = Tr_strcmpExp(oper, left.exp, right.exp);
				return expTy(e, Ty_Int());
			}
			// compare
			else if (oper == A_eqOp || oper == A_neqOp) {
				if (compatible(actual_ty(left.ty), actual_ty(right.ty))) {
					switch (actual_ty(left.ty)->kind) {
						case Ty_int: case Ty_record: case Ty_array: case Ty_nil:
							return expTy(Tr_opExp(oper, left.exp, right.exp), Ty_Int());
						case Ty_string: 
							return expTy(Tr_strcmpExp(oper, left.exp, right.exp), Ty_Int());
						default: EM_error(get_opexp_leftpos(a), "expression doesn't support equal comparing");
					}
				}
				else {
					EM_error(a->pos, "same type required");
				}
			}
			break;
		}
		case A_varExp: {
			return transVar(venv, tenv, a->u.var, l, label);
		}
		case A_nilExp: {
			return expTy(Tr_nilExp(), Ty_Nil());
		}
		case A_intExp: {
			return expTy(Tr_intExp(a->u.intt), Ty_Int());
		}
		case A_stringExp: {
			return expTy(Tr_strExp(a->u.stringg), Ty_String());
		}
		case A_ifExp: {
			struct expty testty = transExp(venv, tenv, get_ifexp_test(a), l, label);
			if (actual_ty(testty.ty) != Ty_Int()) {
				EM_error(a->u.iff.test->pos, "expression must be integer");
			}
			struct expty thenty = expTy(NULL, Ty_Void());
			if (a->u.iff.then) {
				thenty = transExp(venv, tenv, a->u.iff.then, l, label);
			}
			struct expty elsety = expTy(NULL, Ty_Void());
			if (a->u.iff.elsee) {
				elsety = transExp(venv, tenv, a->u.iff.elsee, l, label);
				if (!compatible(actual_ty(elsety.ty), actual_ty(thenty.ty))) EM_error(a->u.iff.elsee->pos, "then exp and else exp type mismatch");
			}
			else {
				if (thenty.ty->kind != Ty_void) EM_error(a->u.iff.then->pos, "if-then exp's body must produce no value");
			}
			return expTy(Tr_ifExp(testty.exp, thenty.exp, elsety.exp), thenty.ty);
		}
		// record creation
		case A_recordExp: {
			Ty_ty x = actual_ty(S_look(tenv, get_recordexp_typ(a)));
			if (!x) {
				EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
				return expTy(Tr_nilExp(), Ty_Nil());
			}
			if (x->kind == Ty_record) {
				A_efieldList efl;
				Ty_fieldList tfl;
				int fieldCnt = 0;
				Tr_fieldList fields = NULL;
				for (efl = a->u.record.fields, tfl = x->u.record; efl && tfl; efl = efl->tail, tfl = tfl->tail) {
					struct expty e = transExp(venv, tenv, efl->head->exp, l, label);
					if (!compatible(actual_ty(tfl->head->ty), actual_ty(e.ty)) || efl->head->name != tfl->head->name) {
						EM_error(a->pos, "type mismatch");
					}
					Tr_field fld = Tr_Field(fieldCnt++, e.exp);
					fields = Tr_FieldList(fld, fields);
				}
				if (efl) {
					EM_error(a->pos, "Too much fields\n");
				}
				if (tfl) {
					EM_error(a->pos, "Too few fields\n");
				}
				Tr_exp res = Tr_recordAlloc(fieldCnt, fields);
				return expTy(res, x);
			}
			else {
				EM_error(a->pos, "record expected");
			}
			return expTy(Tr_nilExp(), Ty_Nil());
		}
		// Array creation
		case A_arrayExp: {
			Ty_ty arrTy = actual_ty(S_look(tenv, get_arrayexp_typ(a)));
			if (!arrTy) {
				EM_error(a->pos, "undefined type %s", S_name(get_arrayexp_typ(a)));
				return expTy(Tr_nilExp(), Ty_Nil());
			}
			struct expty size;
			size = transExp(venv, tenv, a->u.array.size, l, label);
			struct expty init;
			init = transExp(venv, tenv, a->u.array.init, l, label);
			Tr_exp e = NULL;
			if (arrTy->kind == Ty_array) {
				if (size.ty->kind != Ty_int) {
					EM_error(a->u.array.size->pos, "exp's range type is not integer");
					goto done;
				}
				if (! compatible(actual_ty(arrTy->u.array), actual_ty(init.ty))) {
					EM_error(get_arrayexp_init(a)->pos, "type mismatch");
					goto done;
				}
				e = Tr_arrayAlloc(size.exp, init.exp);
			}
			else {
				EM_error(a->pos, "%s is not a type of array", S_name(a->u.array.typ));
			}
			done:
			return expTy(e, arrTy);
		}
		case A_whileExp: {
			struct expty testty = transExp(venv, tenv, a->u.whilee.test, l, label);
			if (actual_ty(testty.ty) != Ty_Int()) {
				EM_error(a->pos, "expression must be integer");
			}
			S_beginScope(venv);
			Tr_access looplabel = Tr_allocLocal(l, TRUE);
			S_enter(venv, S_Symbol("<loop>"), E_VarEntry(looplabel, Ty_Void()));
			Temp_label done = Temp_newlabel();
			struct expty bodyty = transExp(venv, tenv, a->u.whilee.body, l, done);
			if (actual_ty(bodyty.ty) != Ty_Void()) EM_error(a->pos, "while body must produce no value");
			S_endScope(venv);
			return expTy(Tr_whileExp(testty.exp, bodyty.exp, done), Ty_Void());
		}
		case A_forExp: {
			struct expty loty = transExp(venv, tenv, a->u.forr.lo, l, label);
			if (loty.ty != Ty_Int()) EM_error(get_forexp_lo(a)->pos, "for exp's range type is not integer");
			struct expty hity = transExp(venv, tenv, a->u.forr.hi, l, label);
			if (actual_ty(hity.ty) != Ty_Int()) EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
			S_beginScope(venv);
			Tr_access loopvar = Tr_allocLocal(l, TRUE);
			Tr_access looplabel = Tr_allocLocal(l, TRUE);
			Temp_label done = Temp_newlabel();
			S_enter(venv, a->u.forr.var, E_ROVarEntry(loopvar, Ty_Int()));
			// S_enter(venv, protect(a->u.forr.var), E_ROVarEntry(loopvar, Ty_Int()));
			S_enter(venv, S_Symbol("<loop>"), E_ROVarEntry(looplabel, Ty_Void()));
			struct expty bodyty = transExp(venv, tenv, a->u.forr.body, l, done);
			if (actual_ty(bodyty.ty) != Ty_Void()) EM_error(a->u.forr.body->pos, "for body must produce no value");
			S_endScope(venv);
			return expTy(Tr_forExp(loopvar, loty.exp, hity.exp, bodyty.exp, done), Ty_Void());
		}
		case A_callExp: {
			E_enventry x = S_look(venv, a->u.call.func);
			if (x && x->kind == E_funEntry) {
				Ty_tyList argty = x->u.fun.formals;
				A_expList arg = a->u.call.args;
				Tr_expList el = NULL;
				//Tr_accessList al = NULL;
				while (argty) {
					if (!arg) {
						EM_error(arg->head->pos, "too few params in function %s", S_name(a->u.call.func));
						break;
					}
					struct expty ty = transExp(venv, tenv, arg->head, l, label);
					if (!compatible(actual_ty(ty.ty), actual_ty(argty->head))) {
						EM_error(arg->head->pos, "para type mismatch");
						break;  // should I continue checking the rest?
					}
					// Fixed params order
					el = Tr_append(el, ty.exp);
					// ** Leaving allocate space of function arguments to prologue
					// Tr_access acc1 = Tr_allocLocal(l, TRUE);
					// al = Tr_AccessList(acc1, al);
					argty = argty->tail;
					arg = arg->tail;
				}
				if (arg) EM_error(arg->head->pos, "too many params in function %s", S_name(a->u.call.func));
				Tr_exp e = Tr_callExp(l, get_func_level(x), get_func_label(x), el);
				return expTy(e, x->u.fun.result);
			}
			else {
				if (!x) EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
				else EM_error(a->pos, "%s is not a function", S_name(a->u.call.func));
			}
			return expTy(Tr_noop(), Ty_Void());
		}
		case A_assignExp: {
			struct expty varty = transVar(venv, tenv, a->u.assign.var, l, label);
			struct expty exp_ty = transExp(venv, tenv, a->u.assign.exp, l, label);
			if (!compatible(actual_ty(exp_ty.ty), actual_ty(varty.ty))) EM_error(a->pos, "unmatched assign exp");
			if (get_assexp_var(a)->kind == A_simpleVar) {
				E_enventry x = S_look(venv, get_simplevar_sym(get_assexp_var(a)));
				if (x && x->readonly) EM_error(a->pos, "loop variable can't be assigned");
			}
			return expTy(Tr_assignExp(varty.exp, exp_ty.exp), Ty_Void());
		}
		case A_letExp: {
			struct expty exp;
			A_decList d;
			S_beginScope(venv);
			S_beginScope(tenv);
			Tr_expList el = NULL;
			Tr_expList tail = NULL;
			for (d = a->u.let.decs; d; d=d->tail) {
				Tr_exp e = transDec(venv, tenv, d->head, l, label);
				if (tail) {
					tail->tail = Tr_ExpList(e, NULL);
					tail = tail->tail;
				}
				else {
					el = Tr_ExpList(e, NULL);
					tail = el;
				}
			}
			exp = transExp(venv, tenv, get_letexp_body(a), l, label);
			S_endScope(tenv);
			S_endScope(venv);
			return expTy(Tr_letExp(el, exp.exp), exp.ty);
		}
		case A_seqExp: {
			A_expList list = a->u.seq;
			Tr_exp res = Tr_noop();
			struct expty retty = expTy(Tr_noop(), Ty_Void());
			while (list) {
				retty = transExp(venv, tenv, list->head, l, label);
				res = Tr_seqExp(res, retty.exp);
				list = list->tail;
			}
			return expTy(res, retty.ty);
		}
		case A_breakExp: {
			if (label) {
				return expTy(Tr_breakExp(label), Ty_Void());
			}
			else {
				EM_error(a->pos, "Break must be in a loop");
				return expTy(Tr_noop(), Ty_Void());
			}
		}
	}
	assert(0);
	return expTy(Tr_nilExp(), Ty_Void());
}

U_boolList fieldL2boolL(A_fieldList fl)
{
	U_boolList bl = NULL;
	U_boolList btail = NULL;
	A_fieldList cur = fl;
	while (fl) {
		if (btail) {
			btail->tail = U_BoolList(fl->head->escape, NULL);
			btail = btail->tail;
		}
		else {
			bl = U_BoolList(fl->head->escape, NULL);
			btail = bl;
		}
		fl = fl->tail;
	}
	return bl;
}

// make function formals type list
Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params)
{
	if (!params) return NULL;
	Ty_ty x = S_look(tenv, params->head->typ);
	if (!x) EM_error(params->head->pos, "undefined type %s", S_name(params->head->typ));
	else return Ty_TyList(x, makeFormalTyList(tenv, params->tail));
}

int updateTenv(Ty_ty newty, A_namety n, Ty_ty entry)
{
	switch(n->ty->kind) {
		case A_nameTy: {
			// entry->u.name.sym = newty->u.name.sym;
			entry->u.name.ty = newty;
			break;
		}
		case A_recordTy: {
			entry->kind = Ty_record;
			entry->u.record = newty->u.record;
			break;
		}
		case A_arrayTy: {
			entry->kind = Ty_array;
			entry->u.array = newty->u.array;
			break;
		}
		default: assert(0);
	}
	return 0;
}

Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level l, Temp_label label)
{
	switch(d->kind) {
		// A variable declare
		case A_varDec: {
			E_enventry x = S_look(venv, get_vardec_var(d));
			/*
			// check duplicate symbol
			if (x && x->kind == E_varEntry) {
				EM_error(d->pos, "two variables have the same name");
				return Tr_nilExp();
			}
			*/
			// variable type checking
			if (get_vardec_typ(d)) {
				Ty_ty ty = S_look(tenv, get_vardec_typ(d));
				if (!ty) {
					EM_error(d->pos, "undefined type %s", S_name(get_vardec_typ(d)));
					break;
				}
				struct expty ini = transExp(venv, tenv, get_vardec_init(d), l, label);
				// type match checking
				if (!compatible(actual_ty(ty), actual_ty(ini.ty))) {
					EM_error(d->u.var.init->pos, "type mismatch");
				}
				else {
					Tr_access acc = Tr_allocLocal(l, TRUE);
					S_enter(venv, get_vardec_var(d), E_VarEntry(acc, actual_ty(ty)));
					return Tr_assignExp(Tr_simpleVar(acc, l), ini.exp);
				}
			}
			else {
				struct expty ini = transExp(venv, tenv, get_vardec_init(d), l, label);
				// type checking for some decs like var a := 8
				if (get_expty_kind(ini) == Ty_nil) {
					EM_error(d->u.var.init->pos, "init should not be nil without type specified");
					break;
				}
				Tr_access acc = Tr_allocLocal(l, TRUE);
				S_enter(venv, get_vardec_var(d), E_VarEntry(acc, actual_ty(ini.ty)));
				return Tr_varDec(acc, ini.exp);
			}
			break;
		}
		// A type declare
		case A_typeDec: {
			for (A_nametyList list = d->u.type; list; list = list->tail) {
				Ty_ty tmp = S_look(tenv, list->head->name);
				/* xxxx Disabled xxxxx
				if (tmp) {
					EM_error(d->pos, "two types have the same name");
				}
				*/
				S_enter(tenv, list->head->name, Ty_Name(list->head->name, NULL));
			}
			for (A_nametyList list = d->u.type; list; list = list->tail) {
				Ty_ty trans_ty = transTy(tenv, list->head->ty);
				Ty_ty selfty = S_look(tenv, list->head->name);
				if (trans_ty->kind == Ty_name && trans_ty->u.name.ty == selfty) EM_error(list->head->ty->pos, "illegal type cycle");
				updateTenv(trans_ty, list->head, selfty);
			}
			return Tr_noop();
			break;
		}
		// a function declare
		case A_functionDec: {
			for (A_fundecList list = d->u.function; list; list = list->tail) {
				A_fundec f = list->head;
				// check function duplicate
				E_enventry x = S_look(venv, f->name);
				/* DISABLE
				if (x) {
					EM_error(f->pos, "two functions have the same name");
				}
				*/
				
				// result type check
				Ty_ty resultTy;
				if (f->result) {
					resultTy = S_look(tenv, f->result);
					if (!resultTy) {
						EM_error(f->pos, "unknown function result type");
					}
				}
				else {
					resultTy = Ty_Void();
				}

				U_boolList bl = fieldL2boolL(f->params);
				Ty_tyList formalTys = makeFormalTyList(tenv, f->params);
				// TODO: change named label to random label
				Temp_label flabel = Temp_namedlabel(S_name(f->name));
				Tr_level funlevel = Tr_newLevel(l, flabel, bl);
				S_enter(venv, f->name, E_FunEntry(funlevel, flabel, formalTys, resultTy));
			}
			for (A_fundecList list = d->u.function; list; list = list->tail) {
				S_beginScope(venv);
				A_fundec f = list->head;
				E_enventry x = S_look(venv, f->name);
				if (!x) {
					EM_error(d->pos, "function %s not defined", S_name(f->name));
					return Tr_noop();
				}
				else if (x->kind != E_funEntry) 
					EM_error(d->pos, "%s is not a function", S_name(f->name));
				A_fieldList l; Ty_tyList t;
				Tr_accessList params = Tr_formals(x->u.fun.level);
				for (l = f->params, t = get_func_tylist(x); l; 
					l = l->tail, t = t->tail, params = params->tail) {
					S_enter(venv, l->head->name, E_VarEntry(params->head, t->head));
				}
				struct expty bodyty = transExp(venv, tenv, f->body, x->u.fun.level, NULL);
				if (!compatible(actual_ty(bodyty.ty), actual_ty(x->u.fun.result))){
					if (actual_ty(x->u.fun.result)->kind == Ty_void) 
						EM_error(f->body->pos, "procedure returns value");
					else 
						EM_error(f->body->pos, "function body return type mismatch: %s", S_name(f->name));
				} 
				S_endScope(venv);
				Tr_funcDec(x->u.fun.level, bodyty.exp);
			}
			return Tr_noop();
			break;
		}
	}
	assert(0);
}

Ty_ty transTy(S_table tenv, A_ty a)
{
	switch (a->kind) {
		case A_nameTy: {
			Ty_ty self = S_look(tenv, a->u.name);
			if (self->kind == Ty_int || self->kind == Ty_string) return self;
			Ty_ty tmp = self;
			while (tmp && tmp->kind == Ty_name) {
				tmp = S_look(tenv, tmp->u.name.sym);
				if (tmp) {
					self = tmp;
					tmp = tmp->u.name.ty;
				}
				else break;
			}
			return Ty_Name(a->u.name, self);
		}
		case A_recordTy: {
			Ty_fieldList fields = NULL;
			Ty_fieldList tail = fields;
			for (A_fieldList it = a->u.record; it; it = it->tail) {
				Ty_ty fieldty = S_look(tenv, it->head->typ);
				if (!fieldty) EM_error(it->head->pos, "undefined type %s", S_name(it->head->typ));
				Ty_field node = Ty_Field(it->head->name, fieldty);
				if (fields) {
					tail->tail = Ty_FieldList(node, NULL);
					tail = tail->tail;
				}
				else {
					fields = Ty_FieldList(node, NULL);
					tail = fields;
				}
			}
			return Ty_Record(fields);
		}
		case A_arrayTy: {
			Ty_ty arrty = S_look(tenv, a->u.array);
			return Ty_Array(arrty);
			// return Ty_Array(Ty_Name(a->u.array, NULL));
		}
		
		default: ;
	}
	assert(0);
}

F_fragList SEM_transProg(A_exp exp){

	//TODO LAB5: do not forget to add the main frame
	Tr_level outside = Tr_outermost();
	S_table tenv = E_base_tenv();
	S_table venv = E_base_venv();
	struct expty program_ty = transExp(venv, tenv, exp, outside, NULL);
	Tr_funcDec(outside, program_ty.exp);

	return Tr_getResult();
}

