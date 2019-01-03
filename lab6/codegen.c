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
Temp_tempList Temp_splice(Temp_tempList prev, Temp_tempList succ);
void rerange(T_binOp op, T_exp left_old, T_exp right_old, T_exp *left, T_exp *right);

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
  if (inTemplist(t, h)) return t;
  return Temp_TempList(h, t);
}
/*
 * Function: emit
 * Description: append new instruction into 
 * instruction table.
 */
static void emit(AS_instr inst) {
#if _DEBUG_
  static int cnt = 1;
  FILE *file = fopen("__DEBUG_Codegen.md", "a");
  string assem = NULL;
  switch (inst->kind)
  {
  case I_MOVE:
    assem = inst->u.MOVE.assem;
    break;
  case I_OPER:
    assem = inst->u.OPER.assem;
    break;
  case I_LABEL:
    assem = inst->u.LABEL.assem;
    break;
  }
  fprintf(file, "%d. %s\n", cnt++, assem);
  fclose(file);
#endif
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
  iList = F_procEntryExit2(iList);
  list = iList;
  iList = last = NULL;
  return list;
}

/*
 * Function: munchExp
 * Description: maximal munch to process T_exp
 */
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
  if (!args) return NULL;
  Temp_tempList ret = munchArgs(cnt + 1, args->tail);
  if (cnt == 0) {
    Temp_temp src = munchExp(args->head);
    emit(AS_Oper("movq\t`s1, (%rsp)", NULL, L(F_SP(), L(src, NULL)), NULL));
    return ret;
  }
  if (cnt <= 6) {
    Temp_temp dst = r(cnt);
    char buf[ASSEMLEN];
    if (args->head->kind == T_CONST) {
      sprintf(buf, "movq\t$%d, `d0", args->head->u.CONST);
      emit(AS_Oper(String(buf), L(dst, NULL), NULL, NULL));
    }
    else if (args->head->kind == T_NAME) {
      sprintf(buf, "movq\t$.%s, `d0", Temp_labelstring(args->head->u.NAME));
      emit(AS_Oper(String(buf), L(dst, NULL), NULL, NULL));
    }
    else if (args->head->kind == T_MEM) {
      T_exp mem = args->head->u.MEM;
      if (mem->kind == T_BINOP &&
          mem->u.BINOP.op == T_plus &&
          mem->u.BINOP.left->kind == T_CONST &&
          mem->u.BINOP.right->kind == T_BINOP &&
          mem->u.BINOP.right->u.BINOP.op == T_plus &&
          mem->u.BINOP.right->u.BINOP.left->kind == T_NAME &&
          mem->u.BINOP.right->u.BINOP.right->kind == T_TEMP)
      {
        sprintf(buf, "movq\t%d + .%s(`s0), `d0", mem->u.BINOP.left->u.CONST, 
        Temp_labelstring(mem->u.BINOP.right->u.BINOP.left->u.NAME));
        emit(AS_Oper(String(buf), L(dst, NULL), 
        L(mem->u.BINOP.right->u.BINOP.right->u.TEMP, NULL), NULL));
      }
      else {
        Temp_temp src = munchExp(args->head);
        sprintf(buf, "movq\t`s0, `d0");
        emit(AS_Move(String(buf), L(dst, NULL), L(src, NULL)));
      }
    }
    else {
      Temp_temp src = munchExp(args->head);
      sprintf(buf, "movq\t`s0, `d0");
      emit(AS_Move(String(buf), L(dst, NULL), L(src, NULL)));
    }
    return L(dst, ret);
  }
  else {
    char buf[ASSEMLEN];
    if (args->head->kind == T_CONST) {
      sprintf(buf, "movq\t%d, %d(%%rsp)", 
      args->head->u.CONST, F_wordSize * (cnt - 6));
      emit(AS_Oper(String(buf), NULL, L(F_SP(), NULL), NULL));
    }
    else if (args->head->kind == T_NAME) {
      sprintf(buf, "movq\t$.%s, %d(%%rsp)", 
      Temp_labelstring(args->head->u.NAME), F_wordSize * (cnt - 6));
      emit(AS_Oper(String(buf), NULL, L(F_SP(), NULL), NULL));
    }
    else {
      Temp_temp src = munchExp(args->head);
      sprintf(buf, "movq\t`s1, %d(%%rsp)", F_wordSize * (cnt - 6));
      emit(AS_Oper(String(buf), NULL, L(F_SP(), L(src, NULL)), NULL));
    }
    return ret;
  }
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
  char buf[ASSEMLEN];
  T_exp dst = s->u.MOVE.dst, src = s->u.MOVE.src;
  assert(dst->kind == T_TEMP || dst->kind == T_MEM);

  // Move Const -> Temp
  if (src->kind == T_CONST && dst->kind == T_TEMP) {
    sprintf(buf, "movq\t$%d, `d0", src->u.CONST);
    emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), NULL, NULL));
    return;
  } 
  // Move Name -> Temp
  if(src->kind == T_NAME && dst->kind == T_TEMP) {
    sprintf(buf, "movq\t$.%s, `d0", Temp_labelstring(src->u.NAME));
    emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), NULL, NULL));
    return;
  }
  // Move Mem -> Temp
  if (src->kind == T_MEM && dst->kind == T_TEMP) {
    if (src->u.MEM->kind == T_TEMP) {
      sprintf(buf, "movq\t(`s0), `d0");
      emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(src->u.MEM->u.TEMP, NULL), NULL));
      return;
    }
    else if (src->u.MEM->kind == T_BINOP && src->u.MEM->u.BINOP.op == T_plus) {
      T_exp left = NULL, right = NULL;
      rerange(src->u.MEM->u.BINOP.op, src->u.MEM->u.BINOP.left,
              src->u.MEM->u.BINOP.right, &left, &right);
      if (!left) {
        // right is a CONST
        Temp_temp transfer = munchExp(right);
        sprintf(buf, "movq\t(`s0), `d0");
        emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL), NULL));
        return;
      }
      else if (left->kind == T_CONST) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t%d(`s0), `d0", left->u.CONST);
          emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(right->u.TEMP, NULL), NULL));
          return;
        }
        else if (right->kind == T_BINOP && right->u.BINOP.op == T_plus && 
        right->u.BINOP.left->kind == T_NAME && 
        right->u.BINOP.right->kind == T_TEMP)
        {
          sprintf(buf, "movq\t%d + .%s(`s0), `d0", left->u.CONST, 
            Temp_labelstring(right->u.BINOP.left->u.NAME));
          emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), 
            L(right->u.BINOP.right->u.TEMP, NULL), NULL));
          return;
        }
        else if (right->kind == T_BINOP && right->u.BINOP.op == T_plus && 
        right->u.BINOP.left->kind == T_TEMP && 
        right->u.BINOP.right->kind == T_NAME) {
          sprintf(buf, "movq\t%d + .%s(`s0), `d0", left->u.CONST, 
          Temp_labelstring(right->u.BINOP.right->u.NAME));
          emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), 
          L(right->u.BINOP.left->u.TEMP, NULL), NULL));
          return;
        }
        else {
          Temp_temp transfer = munchExp(right);
          sprintf(buf, "movq\t%d(`s0), `d0", left->u.CONST);
          emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL), NULL));
          return;
        }
      }
      else if (left->kind == T_NAME) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t.%s(`s0), `d0", Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(right->u.TEMP, NULL), NULL));
          return;
        }
        else {
          Temp_temp transfer = munchExp(right);
          sprintf(buf, "movq\t.%s(`s0), `d0", Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL), NULL));
          return;
        }
      }
      else {
        Temp_temp transfer = munchExp(src->u.MEM);
        sprintf(buf, "movq\t(`s0), `d0");
        emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL), NULL));
        return;
      }
    }
    else {
      Temp_temp transfer = munchExp(src->u.MEM);
      sprintf(buf, "movq\t(`s0), `d0");
      emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL), NULL));
      return;
    }
  } 
  // Move binary calculation -> Temp
  if (src->kind == T_BINOP && dst->kind == T_TEMP && src->u.BINOP.op == T_plus) {
    T_exp left = NULL, right = NULL;
    rerange(src->u.BINOP.op, src->u.BINOP.left, src->u.BINOP.right, &left, &right);
    if (!left) {
      sprintf(buf, "movq\t$%d, `d0", right->u.CONST);
      emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), NULL, NULL));
      return;
    }
    else if (left->kind == T_CONST) {
      if (right->kind == T_TEMP) {
        sprintf(buf, "leaq\t%d(`s0), `d0", left->u.CONST);
        emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(right->u.TEMP, NULL), NULL));
        return;
      }
      else if (right->kind == T_BINOP && right->u.BINOP.op == T_plus && 
      right->u.BINOP.left->kind == T_NAME && 
      right->u.BINOP.right->kind == T_TEMP)
      {
        sprintf(buf, "leaq\t%d + .%s(`s0), `d0", left->u.CONST, 
          Temp_labelstring(right->u.BINOP.left->u.NAME));
        emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), 
          L(right->u.BINOP.right->u.TEMP, NULL), NULL));
        return;
      }
      else if (right->kind == T_BINOP && right->u.BINOP.op == T_plus && 
      right->u.BINOP.left->kind == T_TEMP && 
      right->u.BINOP.right->kind == T_NAME) {
        sprintf(buf, "leaq\t%d + .%s(`s0), `d0", left->u.CONST, 
        Temp_labelstring(right->u.BINOP.right->u.NAME));
        emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), 
        L(right->u.BINOP.left->u.TEMP, NULL), NULL));
        return;
      }
      else {
        Temp_temp transfer = munchExp(right);
        sprintf(buf, "leaq\t%d(`s0), `d0", left->u.CONST);
        emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL), NULL));
        return;
      }
    }
    else if (left->kind == T_NAME) {
      if (right->kind == T_TEMP) {
        sprintf(buf, "leaq\t.%s(`s0), `d0", Temp_labelstring(left->u.NAME));
        emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(right->u.TEMP, NULL), NULL));
        return;
      }
      else {
        Temp_temp transfer = munchExp(right);
        sprintf(buf, "leaq\t.%s(`s0), `d0", Temp_labelstring(left->u.NAME));
        emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL), NULL));
        return;
      }
    }
    else {
      Temp_temp transfer = munchExp(src);
      sprintf(buf, "movq\t`s0, `d0");
      emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL), NULL));
      return;
    }
  }
  // Move else -> Temp
  if (dst->kind == T_TEMP) {
    Temp_temp transfer = munchExp(src);
    sprintf(buf, "movq\t`s0, `d0");
    emit(AS_Move(String(buf), L(dst->u.TEMP, NULL), L(transfer, NULL)));
    return;
  }

  // Move Const -> Mem
  if (src->kind == T_CONST && dst->kind == T_MEM) {
    if (dst->u.MEM->kind == T_TEMP) {
      sprintf(buf, "movq\t$%d, (`s0)", src->u.CONST);
      emit(AS_Oper(String(buf), NULL, L(dst->u.MEM->u.TEMP, NULL), NULL));
      return;
    }
    else if (dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus) {
      // TODO:
      T_exp left = NULL, right = NULL;
      rerange(dst->u.MEM->u.BINOP.op, dst->u.MEM->u.BINOP.left,
              dst->u.MEM->u.BINOP.right, &left, &right);
      if (!left) {
        Temp_temp transfer = munchExp(right);
        sprintf(buf, "movq\t$%d, (`s0)", src->u.CONST);
        emit(AS_Oper(String(buf), NULL, L(transfer, NULL), NULL));
        return;
      }
      else if (left->kind == T_CONST) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t$%d, %d(`s0)", src->u.CONST, left->u.CONST);
          emit(AS_Oper(String(buf), NULL, L(right->u.TEMP, NULL), NULL));
          return;
        }
        else if (right->kind == T_BINOP && right->u.BINOP.op == T_plus && 
        right->u.BINOP.left->kind == T_NAME && 
        right->u.BINOP.right->kind == T_TEMP)
        {
          sprintf(buf, "movq\t$%d, %d + .%s(`s0)", src->u.CONST, 
            left->u.CONST, Temp_labelstring(right->u.BINOP.left->u.NAME));
          emit(AS_Oper(String(buf), NULL, 
            L(right->u.BINOP.right->u.TEMP, NULL), NULL));
          return;
        }
        else if (right->kind == T_BINOP && right->u.BINOP.op == T_plus && 
        right->u.BINOP.left->kind == T_TEMP && 
        right->u.BINOP.right->kind == T_NAME) {
          sprintf(buf, "movq\t$%d, %d + .%s(`s0)", src->u.CONST, 
          left->u.CONST, Temp_labelstring(right->u.BINOP.right->u.NAME));
          emit(AS_Oper(String(buf), L(dst->u.TEMP, NULL), 
          L(right->u.BINOP.left->u.TEMP, NULL), NULL));
          return;
        }
        else {
          Temp_temp transfer = munchExp(right);
          sprintf(buf, "movq\t$%d, %d(`s0)", src->u.CONST, left->u.CONST);
          emit(AS_Oper(String(buf), NULL, L(transfer, NULL), NULL));
          return;
        }
      }
      else if (left->kind == T_NAME) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t$%d, .%s(`s0)", src->u.CONST, Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), NULL, L(right->u.TEMP, NULL), NULL));
          return;
        }
        else {
          Temp_temp transfer = munchExp(right);
          sprintf(buf, "movq\t$%d, .%s(`s0)", src->u.CONST, Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), NULL, L(transfer, NULL), NULL));
          return;
        }
      }
      else {
        Temp_temp transfer = munchExp(dst->u.MEM);
        sprintf(buf, "movq\t$%d, (`s0)", src->u.CONST);
        emit(AS_Oper(String(buf), NULL, L(transfer, NULL), NULL));
        return;
      }
    }
  }

  // Move Name -> Mem
  if (src->kind == T_NAME && dst->kind == T_MEM) {
    if (dst->u.MEM->kind == T_TEMP) {
      sprintf(buf, "movq\t$.%s, (`s0)", Temp_labelstring(src->u.NAME));
      emit(AS_Oper(String(buf), NULL, L(dst->u.MEM->u.TEMP, NULL), NULL));
      return;
    }
    else if (dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus) {
      T_exp left = NULL, right = NULL;
      rerange(dst->u.MEM->u.BINOP.op, dst->u.MEM->u.BINOP.left,
              dst->u.MEM->u.BINOP.right, &left, &right);
      if (!left) {
        Temp_temp transfer = munchExp(right);
        sprintf(buf, "movq\t$.%s, (`s0)", Temp_labelstring(src->u.NAME));
        emit(AS_Oper(String(buf), NULL, L(transfer, NULL), NULL));
        return;
      }
      else if (left->kind == T_CONST) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t$.%s, %d(`s0)", Temp_labelstring(src->u.NAME), left->u.CONST);
          emit(AS_Oper(String(buf), NULL, L(right->u.TEMP, NULL), NULL));
          return;
        }
        else {
          Temp_temp transfer = munchExp(right);
          sprintf(buf, "movq\t$.%s, %d(`s0)", Temp_labelstring(src->u.NAME), left->u.CONST);
          emit(AS_Oper(String(buf), NULL, L(transfer, NULL), NULL));
          return;
        }
      }
      else if (left->kind == T_NAME) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t$.%s, .%s(`s0)", Temp_labelstring(src->u.NAME), Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), NULL, L(right->u.TEMP, NULL), NULL));
          return;
        }
        else {
          Temp_temp transfer = munchExp(right);
          sprintf(buf, "movq\t$.%s, .%s(`s0)", Temp_labelstring(src->u.NAME), Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), NULL, L(transfer, NULL), NULL));
          return;
        }
      }
      else {
        Temp_temp transfer = munchExp(dst->u.MEM);
        sprintf(buf, "movq\t$.%s, (`s0)", Temp_labelstring(src->u.NAME));
        emit(AS_Oper(String(buf), NULL, L(transfer, NULL), NULL));
        return;
      }
    }
  }

  // Move Temp -> Mem
  if (src->kind == T_TEMP && dst->kind == T_MEM) {
    if (dst->u.MEM->kind == T_TEMP) {
      sprintf(buf, "movq\t`s0, (`s1)");
      emit(AS_Oper(String(buf), NULL, L(src->u.TEMP, L(dst->u.MEM->u.TEMP, NULL)), NULL));
      return;
    }
    else if (dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus) {
      // TODO:
      T_exp left = NULL, right = NULL;
      rerange(dst->u.MEM->u.BINOP.op, dst->u.MEM->u.BINOP.left,
              dst->u.MEM->u.BINOP.right, &left, &right);
      if (!left) {
        Temp_temp transfer = munchExp(right);
        sprintf(buf, "movq\t`s0, (`s1)");
        emit(AS_Oper(String(buf), NULL, L(src->u.TEMP, L(transfer, NULL)), NULL));
        return;
      }
      else if (left->kind == T_CONST) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t`s0, %d(`s1)", left->u.CONST);
          emit(AS_Oper(String(buf), NULL, L(src->u.TEMP, L(right->u.TEMP, NULL)), NULL));
          return;
        }
        else {
          Temp_temp transfer = munchExp(right);
          sprintf(buf, "movq\t`s0, %d(`s1)", left->u.CONST);
          emit(AS_Oper(String(buf), NULL, L(src->u.TEMP, L(transfer, NULL)), NULL));
          return;
        }
      }
      else if (left->kind == T_NAME) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t`s0, .%s(`s1)", Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), NULL, L(src->u.TEMP, L(right->u.TEMP, NULL)), NULL));
          return;
        }
        else {
          Temp_temp transfer = munchExp(right);
          sprintf(buf, "movq\t`s0, .%s(`s1)", Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), NULL, L(src->u.TEMP, L(transfer, NULL)), NULL));
          return;
        }
      }
      else {
        Temp_temp transfer = munchExp(dst->u.MEM);
        sprintf(buf, "movq\t`s0, (`s1)");
        emit(AS_Oper(String(buf), NULL, L(src->u.TEMP, L(transfer, NULL)), NULL));
        return;
      }
    }
  }

  // Move else -> Mem
  if (dst->kind == T_MEM) {
    Temp_temp transfer = munchExp(src);
    if (dst->u.MEM->kind == T_TEMP) {
      sprintf(buf, "movq\t`s0, (`s1)");
      emit(AS_Oper(String(buf), NULL, L(transfer, L(dst->u.MEM->u.TEMP, NULL)), NULL));
      return;
    }
    else if (dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus) {
      // TODO:
      T_exp left = NULL, right = NULL;
      rerange(dst->u.MEM->u.BINOP.op, dst->u.MEM->u.BINOP.left,
              dst->u.MEM->u.BINOP.right, &left, &right);
      if (!left) {
        Temp_temp tmp = munchExp(right);
        sprintf(buf, "movq\t`s0, (`s1)");
        emit(AS_Oper(String(buf), NULL, L(transfer, L(tmp, NULL)), NULL));
        return;
      }
      else if (left->kind == T_CONST) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t`s0, %d(`s1)", left->u.CONST);
          emit(AS_Oper(String(buf), NULL, L(transfer, L(right->u.TEMP, NULL)), NULL));
          return;
        }
        else {
          Temp_temp tmp = munchExp(right);
          sprintf(buf, "movq\t`s0, %d(`s1)", left->u.CONST);
          emit(AS_Oper(String(buf), NULL, L(transfer, L(tmp, NULL)), NULL));
          return;
        }
      }
      else if (left->kind == T_NAME) {
        if (right->kind == T_TEMP) {
          sprintf(buf, "movq\t`s0, .%s(`s1)", Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), NULL, L(transfer, L(right->u.TEMP, NULL)), NULL));
          return;
        }
        else {
          Temp_temp tmp = munchExp(right);
          sprintf(buf, "movq\t`s0, .%s(`s1)", Temp_labelstring(left->u.NAME));
          emit(AS_Oper(String(buf), NULL, L(transfer, L(tmp, NULL)), NULL));
          return;
        }
      }
      else {
        Temp_temp tmp = munchExp(dst->u.MEM);
        sprintf(buf, "movq\t`s0, (`s1)");
        emit(AS_Oper(String(buf), NULL, L(transfer, L(tmp, NULL)), NULL));
        return;
      }
    }
  }
  assert(0);
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
  sprintf(buf, ".%s", S_name(s->u.LABEL));
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

  char buf[ASSEMLEN];
  sprintf(buf, "jmp\t.%s", Temp_labelstring(s->u.JUMP.exp->u.NAME));
  emit(AS_Oper(String(buf), NULL, NULL, AS_Targets(s->u.JUMP.jumps)));
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
  sprintf(compare, "cmp\t`s1, `s0");
  emit(AS_Oper(compare, NULL, L(lefttmp, L(righttmp, NULL)), NULL));
  switch(s->u.CJUMP.op) {
    case T_eq: sprintf(buf, "je\t.`j0"); break;
    case T_ne: sprintf(buf, "jne\t.`j0"); break;
    case T_lt: sprintf(buf, "jl\t.`j0"); break;
    case T_gt: sprintf(buf, "jg\t.`j0"); break;
    case T_le: sprintf(buf, "jle\t.`j0"); break;
    case T_ge: sprintf(buf, "jge\t.`j0"); break;
    case T_ult: sprintf(buf, "jb\t.`j0"); break;
    case T_ule: sprintf(buf, "jbe\t.`j0"); break;
    case T_ugt: sprintf(buf, "ja\t.`j0"); break;
    case T_uge: sprintf(buf, "jae\t.`j0"); break;
  }
  emit(AS_Oper(buf, NULL, NULL, 
        AS_Targets(
          Temp_LabelList(s->u.CJUMP.true, 
            Temp_LabelList(s->u.CJUMP.false, NULL)))));
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
  char buf[ASSEMLEN];
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
  T_exp left = e->u.BINOP.left, right = e->u.BINOP.right;
  if (e->u.BINOP.op == T_mul) {
    // imul S
    if (!(left->kind == T_TEMP && left->u.TEMP == F_RV())) {
      emit(AS_Move("movq\t`s0, %rax", L(F_RV(), NULL), L(munchExp(left), NULL)));
    }
    Temp_temp roprand = munchExp(right);
    Temp_temp backRdx = Temp_newtemp();
    emit(AS_Move("movq\t`s0, `d0", L(backRdx, NULL), L(F_RDX(), NULL)));
    sprintf(buf, "%s\t`s0", opbuf);
    emit(AS_Oper(String(buf), L(F_RV(), L(F_RDX(), NULL)), L(roprand, L(F_RV(), L(F_RDX(), NULL))), NULL));
    Temp_temp ret = Temp_newtemp();
    emit(AS_Move("movq\t%rax, `d0", L(ret, NULL), L(F_RV(), NULL)));
    emit(AS_Move("movq\t`s0, `d0", L(F_RDX(), NULL), L(backRdx, NULL)));
    return ret;
  }
  else if (e->u.BINOP.op == T_div) {
    // idivq S
    if (!(left->kind == T_TEMP && left->u.TEMP == F_RV())) {
      emit(AS_Move("movq\t`s0, %rax", L(F_RV(), NULL), L(munchExp(left), NULL)));
    }
    Temp_temp ret = Temp_newtemp();
    Temp_temp roprand = munchExp(right);
    Temp_temp backupRdx = Temp_newtemp();
    // emit(AS_Oper("movq\t`s0, `d0", L(backupRdx, NULL), L(F_RDX(), NULL), NULL));
    emit(AS_Move("movq\t`s0, `d0", L(backupRdx, NULL), L(F_RDX(), NULL)));
    emit(AS_Oper("cqto", L(F_RV(), L(F_RDX(), NULL)), L(F_RV(), NULL), NULL));
    sprintf(buf, "%s\t`s0", opbuf);
    emit(AS_Oper(String(buf), L(F_RV(), L(F_RDX(), NULL)), L(roprand, L(F_RV(), L(F_RDX(), NULL))), NULL));
    emit(AS_Move("movq\t%rax, `d0", L(ret, NULL), L(F_RV(), NULL)));
    // emit(AS_Oper("movq\t`s0, `d0", L(F_RDX(), NULL), L(backupRdx, NULL), NULL));
    emit(AS_Move("movq\t`s0, `d0", L(F_RDX(), NULL), L(backupRdx, NULL)));
    return ret;
  }
  else {
    // TODO: right can be optimized when mem
    Temp_temp tmp = Temp_newtemp();
    Temp_temp ret = munchExp(left);
    emit(AS_Move("movq\t`s0, `d0", L(tmp, NULL), L(ret, NULL)));
    sprintf(buf, "%s\t`s1, `d0", opbuf);
    emit(AS_Oper(String(buf), L(tmp, NULL), L(tmp, L(munchExp(right), NULL)), NULL));
    return tmp;
  }
}

void rerange(T_binOp op, T_exp left_old, T_exp right_old, T_exp *left, T_exp *right)
{
  if (left_old->kind == T_CONST) {
    if (right_old->kind == T_CONST) {
      switch(op) {
        case T_plus: *right = T_Const(left_old->u.CONST + right_old->u.CONST); left = NULL; return;
        case T_minus: *right = T_Const(left_old->u.CONST - right_old->u.CONST); left = NULL; return;
        case T_mul: *right = T_Const(left_old->u.CONST * right_old->u.CONST); left = NULL; return;
        case T_div: *right = T_Const(left_old->u.CONST / right_old->u.CONST); left = NULL; return;
        case T_and: *right = T_Const(left_old->u.CONST & right_old->u.CONST); left = NULL; return;
        case T_or: *right = T_Const(left_old->u.CONST | right_old->u.CONST); left = NULL; return;
        case T_lshift: *right = T_Const(left_old->u.CONST << right_old->u.CONST); left = NULL; return;
        case T_rshift: *right = T_Const((unsigned int)left_old->u.CONST >> right_old->u.CONST); left = NULL; return;
        case T_arshift: *right = T_Const((signed int)left_old->u.CONST >> right_old->u.CONST); left = NULL; return;
        case T_xor: *right = T_Const(left_old->u.CONST ^ right_old->u.CONST); left = NULL; return;
      }
    }
    *left = left_old;
    *right = right_old;
    return;
  }
  if (right_old->kind == T_CONST) {
    *left = right_old;
    *right = left_old;
    return;
  }
  if (left_old->kind == T_NAME) {
    *left = left_old;
    *right = right_old;
    return;
  }
  if (right_old->kind == T_NAME) {
    *left = right_old;
    *right = left_old;
    return;
  }
  if (left_old->kind == T_TEMP) {
    *left = left_old;
    *right = right_old;
    return;
  }
  if (right_old->kind == T_TEMP) {
    *left = right_old;
    *right = left_old;
  }
  *left = left_old;
  *right = right_old;
  return;
}

/* 
 * Function: C_Mem
 * Description: Generate assembly code for memory access
 */
Temp_temp C_Mem(T_exp e)
{
  char buf[ASSEMLEN];
  if (e->u.MEM->kind == T_TEMP) {
    Temp_temp ret = Temp_newtemp();
    emit(AS_Oper("movq\t(`s0), `d0", L(ret, NULL), L(e->u.TEMP, NULL), NULL));
    return ret;
  }
  if (e->u.MEM->kind == T_BINOP && e->u.MEM->u.BINOP.op == T_plus) {
    T_exp left = NULL, right = NULL;
    rerange(e->u.MEM->u.BINOP.op, e->u.MEM->u.BINOP.left, e->u.MEM->u.BINOP.right, &left, &right);
    if (!left) {
      sprintf(buf, "movq\t$%d, `d0", right->u.CONST);
      Temp_temp tmp = Temp_newtemp();
      emit(AS_Oper(String(buf), L(tmp, NULL), NULL, NULL));
      Temp_temp ret = Temp_newtemp();
      emit(AS_Oper("movq\t(`s0), `d0", L(ret, NULL), L(tmp, NULL), NULL));
      return ret;
    }
    else if (left->kind == T_CONST ) {
      if (right->kind == T_TEMP) {
        Temp_temp ret = Temp_newtemp();
        sprintf(buf, "movq\t%d(`s0), `d0", left->u.CONST);
        emit(AS_Oper(String(buf), L(ret, NULL), L(right->u.TEMP, NULL), NULL));
        return ret;
      }
      else {
        Temp_temp transfer = munchExp(right);
        Temp_temp ret = Temp_newtemp();
        sprintf(buf, "movq\t%d(`s0), `d0", left->u.CONST);
        emit(AS_Oper(String(buf), L(ret, NULL), L(transfer, NULL), NULL));
        return ret;
      }
    }
    else if (left->kind == T_NAME) {
      Temp_temp ret = Temp_newtemp();
      if (right->kind == T_TEMP) {
        sprintf(buf, "movq\t.%s(`s0), `d0", Temp_labelstring(left->u.NAME));
        emit(AS_Oper(String(buf), L(ret, NULL), L(right->u.TEMP, NULL), NULL));
        return ret;
      }
      else {
        Temp_temp transfer = munchExp(right);
        sprintf(buf, "movq\t.%s(`s0), `d0", Temp_labelstring(left->u.NAME));
        emit(AS_Oper(String(buf), L(ret, NULL), L(transfer, NULL), NULL));
        return ret;
      }
    }
    else {
      Temp_temp transfer = munchExp(e->u.MEM);
      Temp_temp ret = Temp_newtemp();
      sprintf(buf, "movq\t(`s0), `d0");
      emit(AS_Oper(String(buf), L(ret, NULL), L(transfer, NULL), NULL));
      return ret;
    }
  }
  else {
    Temp_temp transfer = munchExp(e->u.MEM);
    Temp_temp ret = Temp_newtemp();
    sprintf(buf, "movq\t(`s0), `d0");
    emit(AS_Oper(String(buf), L(ret, NULL), L(transfer, NULL), NULL));
    return ret;
  }
}

/* 
 * Function: C_Temp
 * Description: return temporary access 
 */
Temp_temp C_Temp(T_exp e)
{
  if (e->u.TEMP == F_FP()) {
    Temp_temp ret = Temp_newtemp();
    char buf[ASSEMLEN];
    sprintf(buf, "leaq\t.%s(%%rsp), `d0", Temp_labelstring(framesizeLabel));
    emit(AS_Oper(String(buf), L(ret, NULL), L(F_SP(), NULL), NULL));
    return ret;
  }
  return e->u.TEMP;
}

/*
 * Function: C_Eseq
 * Description: Generate assembly code for sequantial expressions,
 * return the last expression's value if any
 */
Temp_temp C_Eseq(T_exp e)
{
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
  char buf[ASSEMLEN];
  Temp_temp r = Temp_newtemp();
  sprintf(buf, "movq\t$.%s, `d0", Temp_labelstring(e->u.NAME));
  emit(AS_Oper(String(buf), L(r, NULL), NULL, NULL));
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

  int cnt = 0;
  for (Temp_tempList tl = F_argregs(); tl; tl = tl->tail ) {
    char buf[ASSEMLEN];
    sprintf(buf, "movq\t`s0, %d + .%s(%%rsp)", -F_wordSize * (cnt + 3),
            Temp_labelstring(framesizeLabel));
    emit(AS_Oper(String(buf), NULL, L(tl->head, NULL), NULL));
    cnt++;
  }
  emit(AS_Oper("movq\t%r10, -8 + .L14_framesize(%rsp)", NULL, NULL, NULL));
  emit(AS_Oper("movq\t%r11, -16 + .L14_framesize(%rsp)", NULL, NULL, NULL));
  Temp_tempList l = munchArgs(0, e->u.CALL.args);
  string buf = (string) checked_malloc(ASSEMLEN);
  sprintf(buf, "call\t%s", Temp_labelstring(e->u.CALL.fun->u.NAME));
  emit(AS_Oper(buf, L(F_RV(), NULL), l, NULL));
  emit(AS_Oper("movq\t-8 + .L14_framesize(%rsp), %r10", NULL, NULL, NULL));
  emit(AS_Oper("movq\t-16 + .L14_framesize(%rsp), %r11", NULL, NULL, NULL));
  cnt = 0;
  for (Temp_tempList tl = F_argregs(); tl; tl = tl->tail) {
    char buf[ASSEMLEN];
    sprintf(buf, "movq\t%d + .%s(%%rsp), `d0", -F_wordSize * (cnt + 3), Temp_labelstring(framesizeLabel));
    emit(AS_Oper(String(buf), L(tl->head, NULL), NULL, NULL));
    cnt ++;
  }
  Temp_temp r = Temp_newtemp();
  emit(AS_Move("movq\t`s0, `d0", L(r, NULL), L(F_RV(), NULL)));
  return r;
}
