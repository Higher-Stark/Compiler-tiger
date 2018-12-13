%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "errormsg.h"
#include "absyn.h"
#include "y.tab.h"

int charPos=1;

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

int comment = 0;
char string_buf[1024];
char *str;

void clear(char *str_buf, char *str)
{
  memset(str_buf, 0, 1024);
  *str = '\0';
}
%}
  /* You can add lex definitions here. */
digits  [0-9]+

%x COMMENT STR
%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 


<COMMENT>{
  "/*"  {adjust(); comment++;}
  "*"+"/"  {adjust(); comment--; if (comment == 0) BEGIN(INITIAL);}
  "\n"  {adjust(); EM_newline();}
  "*"+[^*/\n]*  adjust();
  . adjust();
  <<EOF>> {adjust(); EM_error(EM_tokPos, "EOF in comment"); return 0;}
}

<STR>{
  \"  {
    charPos += yyleng;
    int length = strlen(string_buf);
    yylval.sval=String(string_buf); 
    clear(string_buf, str); 
    BEGIN(INITIAL); 
    return STRING;
  }
  \n {charPos += yyleng; EM_error(EM_tokPos, "Unterminated string."); clear(string_buf, str); BEGIN(INITIAL);}
  \\[0-9]{3} {
    charPos += yyleng;
    int result;
    (void) sscanf(yytext + 1, "%d", &result );
    
    if (result > 0xff) {
      EM_error(EM_tokPos, "constant out of bound");
    }

    *str++ = result;
  }
  \\^[A-Z] {charPos += yyleng; *str++ = yytext[2] - 'A' + 1;}
  \\n {charPos += yyleng; *str++ = '\n';}
  \\t {charPos += yyleng; *str++ = '\t';}
  \\\"  {charPos += yyleng; *str++ = '\"';}
  \\\\  {charPos += yyleng; *str++ = '\\';}
  \\[ \t\r\n\f]+\\  {charPos += yyleng; continue;}

  . {charPos += yyleng; *str++ = yytext[0];}

  <<EOF>> { EM_error(EM_tokPos, "EOF in string"); return 0;}
}

\"  {adjust(); str = string_buf; BEGIN(STR);}
"/*"  {adjust(); comment++; BEGIN(COMMENT);}

[ \t]* {adjust(); continue;}
"\n"  {adjust(); EM_newline(); continue;}
"\r"  ;
,  {adjust(); return COMMA;}
:  {adjust(); return COLON;}
;  {adjust(); return SEMICOLON;}
"("  {adjust(); return LPAREN;}
")"  {adjust(); return RPAREN;}
"["  {adjust(); return LBRACK;}
"]"  {adjust(); return RBRACK;}
"{"  {adjust(); return LBRACE;}
"}"  {adjust(); return RBRACE;}
"."  {adjust(); return DOT;}
"+"  {adjust(); return PLUS;}
"-"  {adjust(); return MINUS;}
"*"  {adjust(); return TIMES;}
"/"  {adjust(); return DIVIDE;}
"="  {adjust(); return EQ;}
"<>" {adjust(); return NEQ;}
"<"  {adjust(); return LT;}
"<=" {adjust(); return LE;}
">"  {adjust(); return GT;}
">=" {adjust(); return GE;}
"&"  {adjust(); return AND;}
"|"  {adjust(); return OR;}
":=" {adjust(); return ASSIGN;}
array  {adjust(); return ARRAY;}
then {adjust(); return THEN;}
else {adjust(); return ELSE;}
while  {adjust(); return WHILE;}
for  {adjust(); return FOR;}
to {adjust(); return TO;}
do {adjust(); return DO;}
let  {adjust(); return LET;}
in {adjust(); return IN;}
end  {adjust(); return END;}
of {adjust(); return OF;}
break  {adjust(); return BREAK;}
function {adjust(); return FUNCTION;}
if    {adjust(); return IF; }
var  {adjust(); return VAR;}
type  {adjust(); return TYPE;}
nil   {adjust(); return NIL; }
{digits}  {adjust(); yylval.ival=atoi(yytext); return INT;}
[a-zA-Z][a-zA-Z0-9_]*  {adjust(); yylval.sval=String(yytext); return ID;}

. {adjust(); EM_error(EM_tokPos, "Invalid token"); continue;}
<<EOF>> return 0;
%%
