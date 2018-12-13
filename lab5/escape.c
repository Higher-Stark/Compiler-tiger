#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "escape.h"
#include "table.h"
#include "errormsg.h"

/*
 * escapeEntry
 * indicates variable's escape flag and its depth
 */
typedef struct escapeEntry_ *escapeEntry;

struct escapeEntry_ {
    int depth;
    bool *p_escape;
};

escapeEntry EscapeEntry(int d, bool *p);
bool isEscape(escapeEntry e);
int getDepth(escapeEntry e);
void checkEscape(escapeEntry e, int curDepth);

/*
 * constructor
 */
escapeEntry EscapeEntry(int d, bool *p)
{
    escapeEntry e = (escapeEntry) checked_malloc(sizeof(struct escapeEntry_));
    e->depth = d;
    e->p_escape = p;
    return e;
}

/* 
 * get escape attribute
 */
bool isEscape(escapeEntry e)
{
    return *(e->p_escape);
}

/* 
 * get variable depth
 */
int getDepth(escapeEntry e)
{
    return e->depth;
}

/* 
 * check variable's escape attribute
 * if not escape, compare depth and decide escape
 */
void checkEscape(escapeEntry e, int curDepth)
{
    assert(e);
    if (!isEscape(e) && getDepth(e) < curDepth) {
        *(e->p_escape) = TRUE;
    }
    else if (getDepth(e) > curDepth) {
        // internal variable is not expected to be accessed in outer level
        assert(0);
    }
}

static void traverseExp(S_table env, int depth, A_exp e);
static void traverseDec(S_table env, int depth, A_dec d);
static void traverseVar(S_table env ,int depth, A_var v);

void Esc_findEscape(A_exp exp) {
	// TODO:
    S_table env = S_empty();
    S_beginScope(env);
    int mainDepth=1;
    traverseExp(env, mainDepth, exp);
    S_endScope(env);
    free(env);
}

/*
 * function traverseExp
 * traverse expression and mark certain variable escape true
 * @env : variable environment 
 * @depth : current depth
 * @e : expression
 */
static void traverseExp(S_table env, int depth, A_exp e)
{
    // TODO:
    switch(e->kind) {
        case A_varExp: {
            traverseVar(env, depth, e->u.var);
            break;
        }
        case A_nilExp: case A_intExp: case A_stringExp: case A_breakExp:
        break;
        case A_callExp: {
            A_expList el = e->u.call.args;
            while (el) {
                traverseExp(env, depth, el->head);
                el = el->tail;
            }
            break;
        }
        case A_opExp: {
            traverseExp(env, depth, e->u.op.left);
            traverseExp(env, depth, e->u.op.right);
            break;
        }
        case A_recordExp: {
            A_efieldList fields = e->u.record.fields;
            while (fields) {
                traverseExp(env, depth, fields->head->exp);
                fields = fields->tail;
            }
            break;
        }
        case A_seqExp: {
            A_expList el = e->u.seq;
            while (el) {
                traverseExp(env, depth, el->head);
                el = el->tail;
            }
            break;
        }
        case A_assignExp: {
            traverseVar(env, depth, e->u.assign.var);
            traverseExp(env, depth, e->u.assign.exp);
            break;
        }
        case A_ifExp: {
            traverseExp(env, depth, e->u.iff.test);
            traverseExp(env, depth, e->u.iff.then);
            if (e->u.iff.elsee) traverseExp(env, depth, e->u.iff.elsee);
            break;
        }
        case A_whileExp: {
            traverseExp(env, depth, e->u.whilee.test);
            traverseExp(env, depth, e->u.whilee.body);
            break;
        }
        case A_forExp: {
            S_beginScope(env);
            traverseExp(env, depth, e->u.forr.lo);
            traverseExp(env, depth, e->u.forr.hi);
            escapeEntry entry = EscapeEntry(depth, &(e->u.forr.escape));
            S_enter(env, e->u.forr.var, entry);
            traverseExp(env, depth, e->u.forr.body);
            S_endScope(env);
            break;
        }
        case A_letExp: {
            S_beginScope(env);
            for (A_decList decs = e->u.let.decs; decs; decs = decs->tail) {
                traverseDec(env, depth, decs->head);
            }
            traverseExp(env, depth, e->u.let.body);
            S_endScope(env);
            break;
        }
        case A_arrayExp: {
            traverseExp(env, depth, e->u.array.size);
            traverseExp(env, depth, e->u.array.init);
            break;
        }
        default: assert(0);
    }
    return;
}

/* 
 * function traverseDec
 * traverse declaration
 * * add declared variable into env;
 * * ignore type declaration
 * * add function variable into env and traverse body
 * @env : variable environment
 * @depth : current depth(parent depth of function declaration)
 * @d: declaration(s)
 */
static void traverseDec(S_table env, int depth, A_dec d)
{
    // TODO:
    switch(d->kind) {
        case A_varDec: {
            traverseExp(env, depth, d->u.var.init);
            escapeEntry en = EscapeEntry(depth, &(d->u.var.escape));
            S_enter(env, d->u.var.var, en);
            break;
        }
        case A_typeDec: 
        break;
        case A_functionDec: {
            for (A_fundecList funcs = d->u.function; funcs; funcs = funcs->tail) {
                S_beginScope(env);
                for (A_fieldList params = funcs->head->params; params; params = params->tail) {
                    A_field f = params->head;
                    escapeEntry en = EscapeEntry(depth + 1, &(f->escape));
                    S_enter(env, f->name, en);
                }
                traverseExp(env, depth + 1, funcs->head->body);
                S_endScope(env);
            }
            break;
        }
        default: assert(0);
    }
    return ;
}

/* 
 * function traverseVar
 * traverse a variable
 * * simple var, check env and mark escape if necessary;
 * * field var, ignore sym and check var
 * * subscript var, check var and traverse expression
 * @env : variable environment
 * @depth : current depth
 * @v : variable
 */
static void traverseVar(S_table env, int depth, A_var v)
{
    // TODO:
    switch(v->kind) {
        case A_simpleVar: {
            escapeEntry en = S_look(env, v->u.simple);
            if (!en) {
                EM_error(v->pos, "undefined variable %s", v->u.simple);
                return;
            }
            checkEscape(en, depth);
            break;
        }
        case A_fieldVar: {
            traverseVar(env, depth, v->u.field.var);
            break;
        }
        case A_subscriptVar: {
            traverseVar(env ,depth, v->u.subscript.var);
            traverseExp(env, depth, v->u.subscript.exp);
            break;
        }
        default: assert(0);
    }
    return;
}