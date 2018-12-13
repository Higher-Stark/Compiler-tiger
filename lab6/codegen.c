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

//Lab 6: put your code here
static Temp_temp munchExp(T_exp e);
static void munchStm(T_stm s);
Temp_tempList L(Temp_temp h, Temp_tempList t) { return Temp_TempList(h, t); }

static AS_instrList iList = NULL, last = NULL;

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
  switch (e->kind) {
    // memory access 
    case T_MEM: {
      Temp_temp r = Temp_newtemp();
      char buf[1024];
      if (e->u.MEM->kind == T_BINOP) {
        T_exp left = e->u.MEM->u.BINOP.left;
        T_exp right = e->u.MEM->u.BINOP.right;
        int csnt = 0;
        T_exp noncsnt = NULL;
        if (left->kind == T_CONST){
          noncsnt = right;
          csnt = left->u.CONST;
        }
        else if (right->kind == T_CONST) {
          noncsnt = left;
          csnt = right->u.CONST;
        }
        else {
          #if _DEBUG_
          fprintf(stderr, "Load instruction must have a const value\n");
          fflush(stderr);
          assert(0);
          #endif
        }
        sprintf(buf, "LOAD `d0 <- M[`s0 + %d]\n", csnt);
        emit(AS_Oper(buf, Temp_TempList(r, NULL), Temp_TempList(munchExp(noncsnt), NULL), NULL));
      }
      else if (e->u.MEM->kind == T_CONST) {
        sprintf(buf, "LOAD `d0 <- M[`r0 + %d]\n", e->u.MEM->u.CONST );
        emit(AS_Oper(buf, Temp_TempList(r, NULL), NULL, NULL));
      }
      else {
        sprintf(buf, "LOAD `d0 <- M[`s0 + 0]\n");
        emit(AS_oper(buf, Temp_TempList(r, NULL), Temp_TempList(munchExp(e->u.MEM), NULL), NULL));
      }
      return r;
    }
    case T_BINOP: {
      Temp_temp r = Temp_newtemp();
      Temp_tempList lefttmp = NULL, righttmp = NULL;
      string operator = NULL;
      string asmop = NULL;
      switch(e->u.BINOP.op) {
        case T_plus: operator = "+"; asmop = "ADD"; break;
        case T_minus: operator = "-"; asmop = "SUB"; break;
        case T_mul: operator = "*"; asmop = "MUL"; break;
        case T_div: operator = "/"; asmop = "DIV"; break;
        case T_and: operator = "&"; asmop = "AND"; break;
        case T_or: operator = "|"; asmop = "OR"; break;
        case T_lshift: operator = "<<"; asmop = "SHL"; break;
        case T_rshift: operator = ">>"; asmop = "SHR"; break;
        case T_arshift: operator = ">>>"; asmop = "SAR"; break;
        case T_xor: operator = '^'; asmop = "XOR"; break;
        default: operator = "+"; asmop = "ADD";
      }
      if (e->u.BINOP.left->kind == T_CONST) {
        lefttmp = NULL;
      }
      else lefttmp = munchExp(e->u.BINOP.left);
      if (e->u.BINOP.right->kind == T_CONST) {
        righttmp = NULL;
      }
      else righttmp = munchExp(e->u.BINOP.right);
      Temp_tempList value = NULL;
      if (lefttmp && righttmp) value = Temp_TempList(lefttmp, Temp_TempList(righttmp, NULL));
      else if (!lefttmp) value = Temp_TempList(righttmp, NULL);
      else if (!righttmp) value = Temp_TempList(lefttmp, NULL);
      else {
        #if _DEBUG_
        fprintf(stderr, "binary operation expects two non-null operand\n");
        fflush(stderr);
        assert(0);
        #endif;
      }
      // TODO: assemble op select;
      // emit()
    }
  }
}