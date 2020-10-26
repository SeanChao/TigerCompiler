%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "y.tab.h"
#include "errormsg.h"

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
 // printf("%d\n", charPos);
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

void len_adjust(void) {
    charPos+=yyleng;
}

int com_cnt = 0;
char sbuf[100] = "";

int is_digit(char c) { return '0' <= c && c <= '9'; }

/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
char *getstr(char *str) {
    // printf("\nprocessing: %s\n", str);
    size_t size = strlen(str);
    if(size == 0)
        return "";
    char *ret = malloc(sizeof(char) * size);
    char *p = str;
    int pos = 0;
    while (*p != 0) {
        char c = *p;
        if (c != '\\')
            ret[pos++] = c;
        else {
            char next = *(p + 1);
            if (next == 'n') {
                ret[pos++] = '\n';
                p++;
            } else if (next == 't') {
                ret[pos++] = '\t';
                p++;
            } else if (next == '"') {
                ret[pos++] = '"';
                p++;
            } else if (next == '\\') {
                ret[pos++] = '\\';
                p++;  
            } else if (next == '^') {
                ret[pos++] = (*(p+2) - 'A' + 1);
                p += 2;
            } else if (is_digit(next)) {
                char n2 = *(p + 2);
                char n3 = *(p + 3);
                if (n2 == 0 || n3 == 0 || !is_digit(n2) || !is_digit(n3)) {
                    ret[pos++] = c;
                    break;
                }
                char n[3] = {next, n2, n3};
                ret[pos++] = atoi(n);
                p += 3;
            } else {
                //  not a valid escape char
                ret[pos++] = c;
            }
        }
        p++;
    }
    ret[pos] = '\0';
    return ret;
}


%}
  /* You can add lex definitions here. */

digits  [0-9]
alphabet [a-zA-Z]
words   [{digits}{alphabets}]

%Start DEFAULT COMMENT STR
%%


<DEFAULT>if              {adjust(); return IF;}
<DEFAULT>then    {adjust(); return THEN;}
<DEFAULT>else    {adjust(); return ELSE;}
<DEFAULT>while   {adjust(); return WHILE;}
<DEFAULT>for   {adjust(); return FOR;}
<DEFAULT>to    {adjust(); return TO;}
<DEFAULT>do    {adjust(); return DO;}
<DEFAULT>let   {adjust(); return LET;}
<DEFAULT>in    {adjust(); return IN;}
<DEFAULT>end   {adjust(); return END;}
<DEFAULT>of    {adjust(); return OF;}
<DEFAULT>break   {adjust(); return BREAK;}
<DEFAULT>nil   {adjust(); return NIL;} 
<DEFAULT>function   {adjust(); return FUNCTION;} 
<DEFAULT>var   {adjust(); return VAR;}
<DEFAULT>type    {adjust(); return TYPE;}


<DEFAULT>\<\>    {adjust(); return NEQ;}
<DEFAULT>\<   {adjust(); return LT;}
<DEFAULT>\<=    {adjust(); return LE;}
<DEFAULT>\>   {adjust(); return GT;}
<DEFAULT>\>=    {adjust(); return GE;}
<DEFAULT>&    {adjust(); return AND;}
<DEFAULT>\|    {adjust(); return OR;}
<DEFAULT>:=    {adjust(); return ASSIGN;}
<DEFAULT>array {adjust(); return ARRAY;}
<DEFAULT>,   {adjust(); return COMMA;}
<DEFAULT>=   {adjust(); return EQ;}
<DEFAULT>:   {adjust(); return COLON;}
<DEFAULT>;   {adjust(); return SEMICOLON;}
<DEFAULT>\(    {adjust(); return LPAREN;}
<DEFAULT>\)    {adjust(); return RPAREN;}
<DEFAULT>\[    {adjust(); return LBRACK;}
<DEFAULT>\]    {adjust(); return RBRACK;}
<DEFAULT>\{    {adjust(); return LBRACE;}
<DEFAULT>\}    {adjust(); return RBRACE;}
<DEFAULT>\.    {adjust(); return DOT;}
<DEFAULT>\+   {adjust(); return PLUS;}
<DEFAULT>\-   {adjust(); return MINUS;}
<DEFAULT>\*   {adjust(); return TIMES;}
<DEFAULT>\/   {adjust(); return DIVIDE;}

<DEFAULT>[a-zA-Z][_a-zA-Z0-9]*  {adjust(); yylval.sval=String(yytext); return ID;}
<DEFAULT>{digits}+       {adjust(); yylval.ival=atoi(yytext); return INT;}

<DEFAULT>\"     {adjust(); BEGIN STR;}
<DEFAULT>"/*"     {adjust();com_cnt++;BEGIN COMMENT;continue;}


<DEFAULT>"\n" {adjust(); EM_newline(); continue;}
<DEFAULT>" "        {adjust();continue;}
<DEFAULT>"\t"        {adjust();continue;}
<DEFAULT>.      {adjust(); EM_error(EM_tokPos, strcat("Illegal token: ", yytext));}

<STR>\\\"       {len_adjust(); strcat(sbuf, "\""); }
<STR>\\\\       {len_adjust(); strcat(sbuf, "\\");}
<STR>\\[\n\t\f ]+\\     {len_adjust();}
<STR>\\         {len_adjust();}
<STR>([_a-zA-Z0-9 \+\-\*\/\.]|\\n|\\t|\\{digits}{3}|\\^{alphabet})+       {len_adjust();strcat(sbuf, getstr(yytext));continue;}
<STR>\"      {len_adjust(); yylval.sval = ((sbuf == NULL) ? NULL : String(sbuf)); sbuf[0]='\0'; BEGIN DEFAULT; return STRING;}

<COMMENT>\/\*       {adjust();com_cnt++;continue;}
<COMMENT>"*/"      {adjust();com_cnt--;if(com_cnt==0) BEGIN DEFAULT;}
<COMMENT>"\n"       {adjust();EM_newline(); continue;}
<COMMENT>.      {adjust();}

<<EOF>>     {yyterminate();}
.   {BEGIN DEFAULT;yyless(0);}

