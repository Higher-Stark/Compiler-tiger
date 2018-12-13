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
const int ASSEMLEN = 64;
static Temp_temp munchExp(T_exp e);
static void munchStm(T_stm s);
Temp_tempList L(Temp_temp h, Temp_tempList t) { return Temp_TempList(h, t); }
Temp_tmepList memAddr(T_exp t_mem, string addr);

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
      char buf[ASSEMLEN];
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
        emit(AS_Oper(buf, L(r, NULL), Temp_TempList(munchExp(noncsnt), NULL), NULL));
      }
      else if (e->u.MEM->kind == T_CONST) {
        sprintf(buf, "LOAD `d0 <- M[`r0 + %d]\n", e->u.MEM->u.CONST );
        emit(AS_Oper(buf, L(r, NULL), NULL, NULL));
      }
      else {
        sprintf(buf, "LOAD `d0 <- M[`s0 + 0]\n");
        emit(AS_oper(buf, Temp_TempList(r, NULL), Temp_TempList(munchExp(e->u.MEM), NULL), NULL));
      }
      return r;
    }
    case T_BINOP: {
      char buf[ASSEMLEN];
      Temp_temp r = Temp_newtemp();
      Temp_tempList lefttmp = NULL, righttmp = NULL;
      string asmop = NULL;
      switch(e->u.BINOP.op) {
        case T_plus:    asmop = "add"; break;
        case T_minus:   asmop = "sub"; break;
        case T_mul:     asmop = "mul"; break;
        case T_div:     asmop = "div"; break;
        case T_and:     asmop = "and"; break;
        case T_or:      asmop = "or";  break;
        case T_lshift:  asmop = "shl"; break;
        case T_rshift:  asmop = "shr"; break;
        case T_arshift: asmop = "sar"; break;
        case T_xor:     asmop = "xor"; break;
        default:        asmop = "add";
      }
      T_exp leftexp = e->u.BINOP.left, rightexp = e->u.BINOP.right;
      char leftbuf[16] = {0}, rightbuf[16] = {0};
      bool exch = false, hasConst = false;

      // left expression
      if (leftexp->kind == T_TEMP) {
        lefttmp = L(leftexp->u.TEMP, NULL);
        sprintf(leftbuf, "%s", "`s0");
      }
      // else if (leftexp->kind == T_MEM) {
      //   lefttmp = munchExp(leftexp);
      //   sprintf(leftbuf, "%s", "`s0");
      // }
      else if (leftexp->kind == T_CONST) {
        hasConst = true;
        sprintf(leftbuf, "%d", leftexp->u.CONST);
      }
      else {
        lefttmp = munchExp(leftexp);
        sprintf(leftbuf, "%s", "`s0");
      }

      // right expression
      if (rightexp->kind == T_TEMP) {
        righttmp = L(rightexp->u.TEMP, NULL);
        sprintf(rightbuf, "%s", hasConst ? "`s0" : "`s1");
      }
      else if (leftexp->kind == T_CONST) {
        if (hasConst) {
          #if _DEBUG_
          fprintf(stderr, "Binary operation doesn't allow two immediates operation");
          fflush(stderr);
          #endif

          assert(0);
        }
        else {
          hasConst = true;
          sprintf(rightbuf, "%d", right->u.CONST);
        }
      }
      else {
        righttmp = munchExp(rightexp);
        sprintf(rightbuf, "%s", hasConst ? "`s0" : "`s1");
      }

      sprintf(buf, "%s\t%s, %s\n", asmop, leftbuf, rightbuf);
      if (lefttmp) {
        Temp_tempList tail = lefttmp;
        while (tail->tail) tail = tail->tail;
        tail->tail = righttmp;
      }
      else lefttmp = righttmp;
      emit(AS_oper(buf, L(r, NULL), lefttmp, NULL));
    }
  }
}