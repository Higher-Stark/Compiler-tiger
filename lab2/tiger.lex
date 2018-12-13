%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "tokens.h"
#include "errormsg.h"

int charPos=1;
int comment = 0;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

void commentopen(void)
{
  comment += 1;
}

void commentclose(void)
{
  comment -= 1;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
char *getstr(const char *str)
{
	//optional: implement this function if you need it
	return NULL;
}

%}
  /* You can add lex definitions here. */
digits  [0-9]+
delim   [ \n\t];

%Start INITIAL COMMENT
%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 

<INITIAL>{delim}  {adjust(); continue;}
<INITIAL>if    {adjust(); return IF; }
<INITIAL>type  {adjust(); return TYPE;}
<INITIAL>nil   {adjust(); return NIL; }
<INITIAL>[a-z][a-z0-9]*  {adjust(); yylval.sval=String(yytext); return ID;}
<INITIAL>{digits}  {adjust(); yylval.ival=atoi(yytext); return INT}
<INITIAL>"/*"   {adjust(); commentopen(); BEGIN INITIAL;}
<COMMENT>"/*"   {adjust(); commentopen(); continue}
<COMMENT>"*/"   {adjust(); commentclose(); }
