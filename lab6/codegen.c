#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"
#include "frame.h"

//Lab 6: put your code here
const int ASSEMLEN = 64;
static Temp_temp munchExp(T_exp e);
static void munchStm(T_stm s);
static Temp_tempList munchArgs(int cnt, T_expList args);
Temp_tempList L(Temp_temp h, Temp_tempList t); 
Temp_tempList memAddr(T_exp mem, string assem, bool issrc);
int getMemAddr(T_exp mem, bool isdst, string addrbuf, Temp_tempList *tmpList, int baseIdx);
Temp_tempList Temp_splice(Temp_tempList prev, Temp_tempList succ);

void C_Move(T_stm s);
void C_Seq(T_stm s);
void C_Label(T_stm s);
void C_Jump(T_stm s);
void C_Cjump(T_stm s);
void C_Exp(T_stm s);

Temp_temp C_Binop(T_exp e);
Temp_temp C_Mem(T_exp e);
Temp_temp C_Temp(T_exp e);
Temp_temp C_Eseq(T_exp e);
Temp_temp C_Name(T_exp e);
Temp_temp C_Const(T_exp e);
Temp_temp C_Call(T_exp e);

static AS_instrList iList = NULL, last = NULL;

Temp_tempList L(Temp_temp h, Temp_tempList t) 
{ 
  assert(h);
  return Temp_TempList(h, t);
}
/*
 * Function: emit
 * Description: append new instruction into 
 * instruction table.
 */
static void emit(AS_instr inst) {
  if (last != NULL) {
    last = last->tail = AS_InstrList(inst, NULL);
  } 
  else {
    last = iList = AS_InstrList(inst, NULL);
  }
}

/*
 * Function: F_codegen
 * Description: generate abstract assemble code 
 * with IR tree. stmList should be process by 
 * Canon module.
 */
// TODO: 1. 用Maximal Munch将IR树转换为Assem数据结构
//       2. 用stack pointer SP 代替 frame pointer FP
AS_instrList F_codegen(F_frame f, T_stmList stmList) {
  AS_instrList list;
  T_stmList sl;
  // TODO: initializations as necessary
  for (sl = stmList; sl; sl = sl->tail) 
    munchStm(sl->head);
  F_procEntryExit2(iList);
  list = iList;
  iList = last = NULL;
  return list;
}

/*
 * Function: munchExp
 * Description: maximal munch to process T_exp
 */
// TODO: maximal munch 
static Temp_temp munchExp(T_exp e) {
  // for storing assembly instruction
  string buf = (string) malloc(ASSEMLEN);

  switch (e->kind) {
    // memory access (without modification)
    case T_MEM: {
      return C_Mem(e);
    }
    // Binary operation
    case T_BINOP: {
      return C_Binop(e);
    }
    // Temp: abstract register
    case T_TEMP: {
      return C_Temp(e);
    }
    // ESEQ: sequential expressions
    case T_ESEQ: {
      return C_Eseq(e);
    }
    // NAME: a label
    case T_NAME: {
      return C_Name(e);
    }
    // Const: constant
    case T_CONST: {
      return C_Const(e);
    }
    // Call: function call
    case T_CALL: {
      return C_Call(e);
    }
  }
  assert(0);
}

/* 
 * Function: getMemAddr
 * Description: get memory address in form of IMM(REG),
 * addrbuf and tmpList is returned value
 */
int getMemAddr(T_exp mem, bool isdst, string addrbuf, Temp_tempList *tmpList, int baseIdx)
{
  char ch = isdst ? 'd' : 's';
  if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus) {
    T_exp leftexp = mem->u.BINOP.left, rightexp = mem->u.BINOP.right;
    if (leftexp->kind == T_CONST && rightexp->kind == T_TEMP) {
      sprintf(addrbuf, "%d(`%c%d)", leftexp->u.CONST, ch, baseIdx);
      *tmpList = L(rightexp->u.TEMP, NULL);
      return 1;
    }
    else if (leftexp->kind == T_TEMP && rightexp->kind == T_CONST) {
      sprintf(addrbuf, "%d(`%c%d)", rightexp->u.CONST, ch, baseIdx);
      *tmpList = L(leftexp->u.TEMP, NULL);
      return 1;
    }
    else {
      Temp_temp transfer = munchExp(mem);
      sprintf(addrbuf, "0x0(`%c%d)", ch, baseIdx);
      *tmpList = L(transfer, NULL);
      return 1;
    }
  }
  else if (mem->kind == T_TEMP) {
    sprintf(addrbuf, "0x0(`%c%d)", ch, baseIdx);
    *tmpList = L(mem->u.TEMP, NULL);
    return 1;
  }
  else if (mem->kind == T_CONST) {
    Temp_temp transfer = Temp_newtemp();
    string loadConst = (string) checked_malloc(ASSEMLEN);
    sprintf(loadConst, "movq\t%d, `d0", mem->u.CONST);
    emit(AS_Move(loadConst, L(transfer, NULL), NULL));
    sprintf(addrbuf, "0x0(`%c%d)", ch, baseIdx);
    *tmpList = L(transfer, NULL);
    return 1;
  }
  else {
    sprintf(addrbuf, "0x0(`%c%d)", ch, baseIdx);
    *tmpList = L(munchExp(mem), NULL);
    return 1;
  }
  return 0;
}

static void munchStm(T_stm s)
{
  string buf = (string) checked_malloc(ASSEMLEN);
  switch(s->kind) {
    case T_SEQ: {
      C_Seq(s); return;
    }
    case T_LABEL: {
      C_Label(s);
      return;
    }
    case T_JUMP: {
      // exp in JUMP must be symbol
      C_Jump(s);
      return;
    }
    case T_CJUMP: {
      C_Cjump(s);
      return;
    }
    case T_MOVE: {
      C_Move(s);
      return;
    }
    case T_EXP: {
      C_Exp(s);
      return;
    }
  }
  assert(0);
}

/*
 * Function: munchArgs
 * Description: put every argument into proper position
 */
Temp_tempList munchArgs(int cnt, T_expList args)
{
  T_expList e = args;
  int cursor = 0;
  while (e && cursor < cnt) {
    e = e->tail;
    cursor++;
  }
  if (!e) return NULL;

  string dest = NULL;
  Temp_temp destreg = NULL;
  if (cnt > 0 && cnt <= 6) {
    dest = name_r(cnt);
    destreg = r(cnt);
  }
  else if (cnt == 0) {
    dest = "-8(%rsp)";
  }
  else {
    dest = (string) checked_malloc(16);
    sprintf(dest, "-%d(%%rsp)", F_wordSize * cnt - 5);
  }
  string buf = (string)checked_malloc(ASSEMLEN);
  sprintf(buf, "movq\t`s0, %s", dest);
  Temp_temp r = munchExp(e->head);
  Temp_tempList rr = NULL;
  if (destreg)
    rr = L(destreg, NULL);
  emit(AS_Move(buf, rr, L(r, NULL)));
  return rr;
}

/*
 * Function : C_Move
 * Description : Generate assembly code for Move statement.
 * * movq  Src,      Dst
 *        <reg>,    <reg>
 *        <reg>,    <mem>
 *        <mem>,    <reg>
 *       <const>,   <reg>
 *       <const>,   <mem>
 */
void C_Move(T_stm s) 
{
  string buf = (string) checked_malloc(ASSEMLEN);
  char instr[8] = "movq";
  char movsrc[16], movdst[16];
  T_exp dst = s->u.MOVE.dst, src = s->u.MOVE.src;
  Temp_tempList dsttmps = NULL, srctmps = NULL;
  assert(dst->kind == T_TEMP || dst->kind == T_MEM);

  // generate destination part
  if (dst->kind == T_TEMP) {
    sprintf(movdst, "`d0");
    dsttmps = L(dst->u.TEMP, NULL);
  }
  else {
    // Move memory to memory is not allowed
    assert(src->kind != T_MEM);
    getMemAddr(dst, TRUE, movdst, &dsttmps, 0);
  }

  // generate source part
  if (src->kind == T_TEMP) {
    sprintf(movsrc, "`s0");
    srctmps = L(src->u.TEMP, NULL);
  }
  else if (src->kind == T_MEM) {
    getMemAddr(src, FALSE, movsrc, &srctmps, 0);
  }
  else {
    srctmps = L(munchExp(src), NULL);
    sprintf(movsrc, "`s0");
  }

  sprintf(buf, "%s\t%s, %s", instr, movsrc, movdst);
  emit(AS_Move(buf, dsttmps, srctmps));
}

/* 
 * Function: C_Seq
 * Description: Generate assembly code for Sequatial Statement
 */
void C_Seq(T_stm s)
{
  munchStm(s->u.SEQ.left);
  munchStm(s->u.SEQ.right);
}

/* 
 * Function : C_Label
 * Description : Generate asembly code for Label statement
 * * <Label>:
 */
void C_Label(T_stm s)
{
  string buf = (string) checked_malloc(ASSEMLEN);
  sprintf(buf, "%s", S_name(s->u.LABEL));
  emit(AS_Label(buf, s->u.LABEL));
}

/* 
 * Function: C_Jump
 * Description: Generate assembly code for Jump statement
 * * jmp <Label>
 * * jmp *<Operand>
 */
void C_Jump(T_stm s)
{
  // assert(s->u.JUMP.exp->kind == T_NAME);

  string buf = (string) checked_malloc(ASSEMLEN);
  if (s->u.JUMP.exp->kind == T_NAME) {
    sprintf(buf, "jmp\t%s", S_name(s->u.JUMP.exp->u.NAME));
    // TODO: jumps not needed?
    emit(AS_Oper(buf, NULL, NULL, NULL));
  }
  else {
    sprintf(buf, "jmp\t`j0");
    emit(AS_Oper(buf, NULL, NULL, AS_Targets(s->u.JUMP.jumps)));
  }
}

/* 
 * Function: C_Cjump
 * Description: Generate assembly code for Conditional Jump statement
 * first compare left and right
 * then jump according to the condition
 */
void C_Cjump(T_stm s)
{
  string buf = (string) checked_malloc(ASSEMLEN);
  T_exp left = s->u.CJUMP.left, right = s->u.CJUMP.right;
  Temp_temp lefttmp = munchExp(left), righttmp = munchExp(right);
  string compare = (string) checked_malloc(ASSEMLEN);
  sprintf(compare, "cmp\t`s0, `s1");
  emit(AS_Oper(compare, NULL, L(lefttmp, L(righttmp, NULL)), NULL));
  switch(s->u.CJUMP.op) {
    case T_eq: sprintf(buf, "je\t`j0"); break;
    case T_ne: sprintf(buf, "jne\t`j0"); break;
    case T_lt: sprintf(buf, "jl\t`j0"); break;
    case T_gt: sprintf(buf, "jg\t`j0"); break;
    case T_le: sprintf(buf, "jle\t`j0"); break;
    case T_ge: sprintf(buf, "jge\t`j0"); break;
    case T_ult: sprintf(buf, "jb\t`j0"); break;
    case T_ule: sprintf(buf, "jbe\t`j0"); break;
    case T_ugt: sprintf(buf, "ja\t`j0"); break;
    case T_uge: sprintf(buf, "jae\t`j0"); break;
  }
  emit(AS_Oper(buf, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
}

/* 
 * Function: C_Exp
 * Description: Generate assembly code for Expression statement
 */
void C_Exp(T_stm s)
{
  munchExp(s->u.EXP);
}

/* 
 * Function: C_Binop
 * Description: Generate asembly code for binary operation
 * * <op> S, D : add, sub, and, or, xor destination by source
 * * imulq/idivq S : multipl/divide %rax by S
 * * <shift> k, D : shift desination by k bits
 * 
 * ** Perform necessary transfer to preserve operand value **
 */
Temp_temp C_Binop(T_exp e)
{
  // TODO:
  string buf = (string) checked_malloc(ASSEMLEN);
  char opbuf[6], loprand[16], roprand[16];
  Temp_tempList ltmpl = NULL, rtmpl = NULL;

  switch(e->u.BINOP.op) {
    case T_plus: sprintf(opbuf, "addq"); break;
    case T_minus: sprintf(opbuf, "subq"); break;
    case T_mul: sprintf(opbuf, "imulq"); break;
    case T_div: sprintf(opbuf, "idivq"); break;
    case T_and: sprintf(opbuf, "and"); break;
    case T_or: sprintf(opbuf, "orq"); break;
    case T_xor: sprintf(opbuf, "xorq"); break;
    case T_lshift: sprintf(opbuf, "shl"); break;
    case T_rshift: sprintf(opbuf, "shr"); break;
    case T_arshift: sprintf(opbuf, "sar"); break;
  }
  Temp_temp transfer = Temp_newtemp();
  T_exp left = e->u.BINOP.left, right = e->u.BINOP.right;
  if (e->u.BINOP.op == T_mul || e->u.BINOP.op == T_div) {
    // TODO: imulq S / idivq S, 
    if (left->kind == T_TEMP) {
      if (left->u.TEMP != F_RV())
        emit(AS_Move("movq\t`s0, %rax", L(F_RV(), NULL), L(left->u.TEMP, NULL)));
    }
    else if (left->kind == T_MEM) {
      getMemAddr(left, FALSE, loprand, &ltmpl, 0);
      char buf[ASSEMLEN];
      sprintf(buf, "movq\t%s, %%rax", loprand);
      emit(AS_Move(String(buf), L(F_RV(), NULL), ltmpl));
    }
    else {
      Temp_temp tmp = munchExp(left);
      emit(AS_Move("movq\t`s0, %rax", L(F_RV(), NULL), L(tmp, NULL)));
    }

    if (right->kind == T_TEMP) {
      sprintf(buf, "%s\t`s0", opbuf);
      emit(AS_Oper(buf, L(F_RV(), NULL), L(right->u.TEMP, NULL), NULL));
    }
    else if (right->kind == T_MEM) {
      getMemAddr(right, FALSE, roprand, &rtmpl, 0);
      sprintf(buf, "%s\t%s", opbuf, roprand);
      emit(AS_Oper(buf, L(F_RV(), NULL), rtmpl, NULL));
    }
    else {
      Temp_temp tmp = munchExp(right);
      sprintf(buf, "%s\t`s0", opbuf);
      emit(AS_Oper(buf, L(F_RV(), NULL), L(tmp, NULL), NULL));
    }
    // FIXME: return %rax
    return F_RV();
  }
  else {
    if (left->kind == T_TEMP) {
      assert(right->kind != T_NAME);
      if (right->kind == T_TEMP) {
        emit(AS_Move("movq\t`s1, `d0", L(left->u.TEMP, NULL), L(left->u.TEMP, L(right->u.TEMP, NULL))));
      }
      else transfer = munchExp(right);
      sprintf(buf, "%s\t`s1, `d0", opbuf);
      emit(AS_Oper(buf, L(left->u.TEMP, NULL), L(left->u.TEMP, L(transfer, NULL)), NULL));
      return transfer;
    }
    else if (left->kind == T_MEM) {
      if (right->kind == T_MEM) {
        transfer = munchExp(left);
        getMemAddr(right, FALSE, loprand, &ltmpl, 1);
        sprintf(buf, "%s\t%s, `d0", opbuf, loprand);
        emit(AS_Oper(buf, L(transfer, NULL), L(transfer, ltmpl), NULL));
        return transfer;
      }
      else if (right->kind == T_TEMP) {
        transfer = munchExp(left);
        sprintf(buf, "%s\t`s1, `d0", opbuf);
        emit(AS_Oper(buf, L(transfer, NULL), L(transfer, L(right->u.TEMP, NULL)), NULL));
        return transfer;
      }
      else if (right->kind == T_CONST) {
        ltmpl = L(munchExp(left), NULL);
        sprintf(buf, "%s\t$%d, `d0", opbuf, right->u.CONST);
        emit(AS_Oper(buf, ltmpl, ltmpl, NULL));
        return ltmpl->head;
      }
      else {
        ltmpl = L(munchExp(left), NULL);
        rtmpl = L(munchExp(right), NULL);
        sprintf(buf, "%s\t`s1, `d0", opbuf);
        emit(AS_Oper(buf, ltmpl, Temp_splice(ltmpl, rtmpl), NULL));
        return ltmpl->head;
      }
    }
    else if (left->kind == T_CONST) {
      if (right->kind == T_TEMP) {
        emit(AS_Move("movq\t`s0, `d0", L(transfer, NULL), L(right->u.TEMP, NULL)));
      }
      else {
        transfer = munchExp(right);
      }
      sprintf(buf, "%s\t$%d, `d0", opbuf, left->u.CONST);
      emit(AS_Oper(buf, L(transfer, NULL), L(transfer, NULL), NULL));
      return transfer;
    }
    else {
      assert(left->kind != T_NAME);
      ltmpl = L(munchExp(left), NULL);
      if (right->kind == T_TEMP) {
        rtmpl = L(right->u.TEMP, NULL);
        sprintf(roprand, "`s1");
      }
      else if (right->kind == T_MEM) {
        getMemAddr(right, FALSE, roprand, &rtmpl, 1);
      }
      else if (right->kind == T_CONST) {
        sprintf(roprand, "$%d", right->u.CONST);
      }
      else {
        sprintf(roprand, "`s1");
        rtmpl = L(munchExp(right), NULL);
      }
      sprintf(buf, "%s\t%s, `d0", opbuf, roprand);
      emit(AS_Oper(buf, ltmpl, Temp_splice(ltmpl, rtmpl), NULL));
      return ltmpl->head;
    }
  }
  assert(0);
}

/* 
 * Function: C_Mem
 * Description: Generate assembly code for memory access
 */
Temp_temp C_Mem(T_exp e)
{
  string buf = (string) checked_malloc(ASSEMLEN);
  Temp_temp r = Temp_newtemp();
  Temp_temp transfer = NULL;
  T_exp mem = e->u.MEM;
  if (mem->kind == T_BINOP) {
    if (mem->u.BINOP.op == T_plus) {
      if (mem->u.BINOP.left->kind == T_TEMP) {
        if (mem->u.BINOP.right->kind == T_CONST) {
          sprintf(buf, "leaq\t%d(`s0), `d0", mem->u.BINOP.right->u.CONST);
          emit(AS_Oper(buf, L(r, NULL), L(mem->u.BINOP.left->u.TEMP, NULL), NULL));
        }
        else if (mem->u.BINOP.right->kind == T_TEMP) {
          transfer = munchExp(mem);
          sprintf(buf, "leaq\t0x0(`s0), `d0");
          emit(AS_Oper(buf, L(r, NULL), L(transfer, NULL), NULL));
        }
        else {
          transfer = munchExp(mem);
          sprintf(buf, "leaq\t0x0(`s0), `d0");
          emit(AS_Oper(buf, L(r, NULL), L(transfer, NULL), NULL));
        }
        return r;
      }
      else if (mem->u.BINOP.left->kind == T_CONST) {
        if (mem->u.BINOP.right->kind == T_TEMP) {
          sprintf(buf, "leaq\t%d(`s0), `d0", mem->u.BINOP.left->u.CONST);
          emit(AS_Oper(buf, L(r, NULL), L(mem->u.BINOP.right->u.TEMP, NULL), NULL));
        }
        else {
          transfer = munchExp(mem->u.BINOP.right);
          sprintf(buf, "leaq\t%d(`s0), `d0", mem->u.BINOP.left->u.CONST);
          emit(AS_Oper(buf, L(r, NULL), L(transfer, NULL), NULL));
        }
        return r;
      }
      else {
        if (mem->u.BINOP.right->kind == T_CONST) {
          transfer = munchExp(mem->u.BINOP.left);
          sprintf(buf, "leaq\t%d(`s0), `d0", mem->u.BINOP.right->u.CONST);
          emit(AS_Oper(buf, L(r, NULL), L(transfer, NULL), NULL));
        }
        else {
          transfer = munchExp(mem);
          sprintf(buf, "leaq\t0x0(`s0), `d0");
          emit(AS_Oper(buf, L(r, NULL), L(transfer, NULL), NULL));
        }
        return r;
      }
    }
    else {
      transfer = munchExp(mem);
      sprintf(buf, "leaq\t0x0(`s0), `d0");
      emit(AS_Oper(buf, L(r, NULL), L(transfer, NULL), NULL));
      return r;
    }
  }
  else {
    transfer = munchExp(mem);
    sprintf(buf, "leaq\t0x0(`s0), `d0");
    emit(AS_Oper(buf, L(r, NULL), L(transfer, NULL), NULL));
    return r;
  }
  assert(0);
}

/* 
 * Function: C_Temp
 * Description: return temporary access 
 */
Temp_temp C_Temp(T_exp e)
{
  return e->u.TEMP;
}

/*
 * Function: C_Eseq
 * Description: Generate assembly code for sequantial expressions,
 * return the last expression's value if any
 */
Temp_temp C_Eseq(T_exp e)
{
  // TODO:
  munchStm(e->u.ESEQ.stm);
  return munchExp(e->u.ESEQ.exp);
}

/* 
 * Function: C_Name
 * Description: Generate assembly code for label
 * put label as a immediate in assembly
 */
Temp_temp C_Name(T_exp e)
{
  // TODO:
  char buf[ASSEMLEN];
  Temp_temp r = Temp_newtemp();
  sprintf(buf, "movq\t$%s, `d0", Temp_labelstring(e->u.NAME));
  emit(AS_Move(String(buf), L(r, NULL), NULL));
  return r;
}

/* 
 * Function: C_Const
 * Description: Generate assembly code for Constant
 */
Temp_temp C_Const(T_exp e)
{
  Temp_temp r = Temp_newtemp();
  string buf = (string) checked_malloc(ASSEMLEN);
  sprintf(buf, "movq\t$%d, `d0", e->u.CONST);
  emit(AS_Oper(buf, L(r, NULL), NULL, NULL));
  return r;
}

/* 
 * Function: C_Call
 * Description: Generate assembly code for function/procedure call
 */
Temp_temp C_Call(T_exp e)
{
  assert(e->u.CALL.fun->kind == T_NAME);

  // TODO: can calldefs be optimized
  Temp_tempList calldefs = Temp_TempList(F_RV(), callerSaves());
  Temp_tempList l = munchArgs(0, e->u.CALL.args);
  string buf = (string) checked_malloc(ASSEMLEN);
  sprintf(buf, "call\t%s", S_name(e->u.CALL.fun->u.NAME));
  emit(AS_Oper(buf, calldefs, l, NULL));
  Temp_temp r = Temp_newtemp();
  emit(AS_Move("movq\t`s0, `d0", L(r, NULL), L(F_RV(), NULL)));
  return r;
}

Temp_tempList Temp_splice(Temp_tempList prev, Temp_tempList succ)
{
  if (prev) {
    Temp_tempList last = prev;
    while (last->tail) last = last->tail;
    last->tail = succ;
  }
  else {
    prev = succ;
  }
  return prev;
}