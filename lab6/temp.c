/*
 * temp.c - functions to create and manipulate temporary variables which are
 *          used in the IR tree representation before it has been determined
 *          which variables are to go into registers.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"

struct Temp_temp_ {int num;};

int Temp_int(Temp_temp t)
{
	return t->num;
}

string Temp_labelstring(Temp_label s)
{return S_name(s);
}

static int labels = 0;

Temp_label Temp_newlabel(void)
{char buf[100];
 sprintf(buf,"L%d",labels++);
 return Temp_namedlabel(String(buf));
}

/* The label will be created only if it is not found. */
Temp_label Temp_namedlabel(string s)
{return S_Symbol(s);
}

static int temps = 100;

Temp_temp Temp_newtemp(void)
{Temp_temp p = (Temp_temp) checked_malloc(sizeof (*p));
 p->num=temps++;
 {char r[16];
  sprintf(r, "%d", p->num);
  Temp_enter(Temp_name(), p, String(r));
 }
 return p;
}

Temp_tempList Temp_append(Temp_tempList list, Temp_temp t)
{
  Temp_tempList p = list;
  while (p && p->tail) {
    p = p->tail;
  }
  if (!p) {
    if (t)
    return Temp_TempList(t, NULL);
    else return NULL;
  }
  p->tail = Temp_TempList(t, NULL);
  return list;
}

Temp_tempList Temp_splice(Temp_tempList head, Temp_tempList tail)
{
  Temp_tempList p = head;
  while (p && p->tail) {
    p = p->tail;
  }
  if (!p) return tail;
  else {
    p->tail = tail;
  }
  return head;
}

Temp_tempList Temp_Replace(Temp_tempList list, Temp_temp oldt, Temp_temp newt)
{
  Temp_tempList ret = NULL;
  for (Temp_tempList cursor = list; cursor; cursor = cursor->tail) {
    if (cursor->head == oldt) {
      ret = Temp_splice(ret, Temp_TempList(newt, NULL));
    }
    else {
      ret = Temp_splice(ret, Temp_TempList(cursor->head, NULL));
    }
  }
  return ret;
}

Temp_tempList Temp_remove(Temp_tempList list, Temp_temp t)
{
  Temp_tempList ret = NULL;
  for (Temp_tempList l = list; l; l = l->tail) {
    if (l->head == t) continue;
    ret = Temp_append(ret, l->head);
  }
  return ret;
}

bool inTemplist(Temp_tempList tl, Temp_temp t)
{
	for (Temp_tempList l = tl; l; l = l->tail) {
		if (t == l->head) return TRUE;
	}
	return FALSE;
}

struct Temp_map_ {TAB_table tab; Temp_map under;};


Temp_map Temp_name(void) {
 static Temp_map m = NULL;
 if (!m) m=Temp_empty();
 return m;
}

Temp_map newMap(TAB_table tab, Temp_map under) {
  Temp_map m = checked_malloc(sizeof(*m));
  m->tab=tab;
  m->under=under;
  return m;
}

Temp_map Temp_empty(void) {
  return newMap(TAB_empty(), NULL);
}

Temp_map Temp_layerMap(Temp_map over, Temp_map under) {
  if (over==NULL)
      return under;
  else return newMap(over->tab, Temp_layerMap(over->under, under));
}

void Temp_enter(Temp_map m, Temp_temp t, string s) {
  assert(m && m->tab);
  TAB_enter(m->tab,t,s);
}

string Temp_look(Temp_map m, Temp_temp t) {
  string s;
  assert(m && m->tab);
  s = TAB_look(m->tab, t);
  if (s) return s;
  else if (m->under) return Temp_look(m->under, t);
  else return NULL;
}

Temp_tempList Temp_TempList(Temp_temp h, Temp_tempList t) 
{Temp_tempList p = (Temp_tempList) checked_malloc(sizeof (*p));
 p->head=h; p->tail=t;
 return p;
}

Temp_labelList Temp_LabelList(Temp_label h, Temp_labelList t)
{Temp_labelList p = (Temp_labelList) checked_malloc(sizeof (*p));
 p->head=h; p->tail=t;
 return p;
}

static FILE *outfile;
void showit(Temp_temp t, string r) {
  fprintf(outfile, "t%d -> %s\n", t->num, r);
}

void Temp_dumpMap(FILE *out, Temp_map m) {
  outfile=out;
  TAB_dump(m->tab,(void (*)(void *, void*))showit);
  if (m->under) {
     fprintf(out,"---------\n");
     Temp_dumpMap(out,m->under);
  }
}

#if _DEBUG_
void Temp_dumpMap2(FILE *out, Temp_map m, void (*show)(void *key, void *value))
{
  TAB_dump(m->tab, show);
  // if (m->under) {
  //   fprintf(out, "-------------\n");
  //   Temp_dumpMap2(out, m->under, show);
  // }
}
#endif