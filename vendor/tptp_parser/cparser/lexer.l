%{
  #include <stdbool.h>
  #include <stdlib.h>
  #include <string.h>

  /* Keep the generated scanner separate from the token lookahead adapter. */
  #define YY_DECL static int tptp_lex(YYSTYPE *yylval_param, yyscan_t yyscanner)

  #include <lean/lean.h>

  #include "parser.tab.h"
%}

signed_real {sign}{unsigned_real}
unsigned_real ({decimal_fraction}|{decimal_exponent})
decimal_exponent ({integer_digits}|{decimal_fraction}){exponent}{exp_integer}
decimal_fraction {unsigned_integer}{dot}{integer_digits}
exp_integer ({signed_exp_integer}|{integer_digits})
signed_exp_integer {sign}{integer_digits}
signed_rational {sign}{unsigned_rational}
unsigned_rational {unsigned_integer}{slash}{positive_integer}
signed_integer {sign}{unsigned_integer}
unsigned_integer ({zero_numeric}|{positive_integer})
positive_integer {non_zero_numeric}{numeric}*
integer_digits {numeric}{numeric}*
vline [|]
star [*]
comment_block {slash_char}{star}{not_star_slash}{star}{star}*{slash_char}
comment_line {percentage_sign}{printable_char}*
not_star_slash ([^*]*[*][*]*[^/*])*[^*]*
percentage_sign [%]
double_quote ["]
do_char ([\40-\41\43-\133\135-\176]|([\\]["\\]))
single_quote [']
back_quote [`]
sq_char ([\40-\46\50-\133\135-\176]|([\\]['\\]))
sign [+-]
dot [.]
exponent [Ee]
slash_char [/]
slosh_char [\\]
zero_numeric [0]
non_zero_numeric [1-9]
numeric [0-9]
lower_alpha [a-z]
upper_alpha [A-Z]
underscore [_]
alpha ({lower_alpha}|{upper_alpha})
alpha_numeric ({lower_alpha}|{upper_alpha}|{numeric}|{underscore})
dollar [$]
printable_char .
viewable_char [.\n]

single_quoted {single_quote}{sq_char}{sq_char}*{single_quote} 
back_quoted {back_quote}{upper_word} 
distinct_object {double_quote}{do_char}*{double_quote} 
dollar_word {dollar}{alpha_numeric}* 
dollar_dollar_word {dollar}{dollar}{alpha_numeric}* 
upper_word {upper_alpha}{alpha_numeric}* 
lower_word {lower_alpha}{alpha_numeric}* 
real ({signed_real}|{unsigned_real}) 
rational ({signed_rational}|{unsigned_rational}) 
integer ({signed_integer}|{unsigned_integer}) 
slash {slash_char} 
slosh {slosh_char} 
plus [+] 
arrow [>] 
less_sign [<] 
hash [#] 
comment {comment_line}|{comment_block} 

%option noyywrap reentrant bison-bridge
%option extra-type="TptpParseContext *"

%%
[ \t\r\n]+ ;
{comment} ;

"!" { return TOK_EXCLAMATION; }
"!!" { return TOK_DOUBLE_EXCLAMATION; }
"!=" { return TOK_EXCLAMATION_EQUALS; }
"!>" { return TOK_EXCLAMATION_ARROW; }
"$cnf(" { return TOK_DOLLAR_CNF_PARENOPEN; }
"$fof(" { return TOK_DOLLAR_FOF_PARENOPEN; }
"$fot(" { return TOK_DOLLAR_FOT_PARENOPEN; }
"$let(" { return TOK_DOLLAR_LET_PARENOPEN; }
"$tff(" { return TOK_DOLLAR_TFF_PARENOPEN; }
"$thf(" { return TOK_DOLLAR_THF_PARENOPEN; }
"&" { return TOK_AMPERSAND; }
"(" { return TOK_PARENOPEN; }
"(.)" { return TOK_PARENOPEN_DOT_PARENCLOSE; }
")" { return TOK_PARENCLOSE; }
")." { return TOK_PLOSE_DOT; }
")}" { return TOK_PARENCLOSE_BRACECLOSE; }
"," { return TOK_COMMA; }
"-" { return TOK_HYPEN; }
"-->" { return TOK_DOUBLE_HYPHEN_ARROW; }
"." { return TOK_DOT; }
":" { return TOK_COLON; }
":=" { return TOK_COLOR_EQUALS; }
"<<" { return TOK_DOUBLE_LESS_SIGN; }
"<=" { return TOK_LESS_SIGN_EQUALS; }
"<=>" { return TOK_LESS_SIGN_EQUALS_ARROW; }
"<~>" { return TOK_LESS_SIGN_TILDE_ARROW; }
"=" { return TOK_EQUALS; }
"==" { return TOK_DOUBLE_EQUALS; }
"=>" { return TOK_EQUALS_ARROW; }
"?" { return TOK_QUESTION; }
"?*" { return TOK_QUESTION_STAR; }
"??" { return TOK_DOUBLE_QUESTION; }
"@" { return TOK_AT; }
"@+" { return TOK_AT_PLUS; }
"@-" { return TOK_AT_MINUS; }
"@=" { return TOK_AT_EQUALS; }
"@@+" { return TOK_DOUBLE_AT_PLUS; }
"@@-" { return TOK_DOUBLE_AT_MINUS; }
"[" { return TOK_BRACKOPEN; }
"[.]" { return TOK_BRACKOPEN_DOT_BRACKCLOSE; }
"[]" { return TOK_BRACKOPEN_BRACKCLOSE; }
"]" { return TOK_BRACKCLOSE; }
"^" { return TOK_CARET; }
"cnf(" { return TOK_CNF_PARENOPEN; }
"creator(" { return TOK_CREATOR_PARENOPEN; }
"file(" { return TOK_FILE_PARENOPEN; }
"fof"[ \t\r\n]*"(" { return TOK_FOF_PARENOPEN; }
"include(" { return TOK_INCLUDE_PARENOPEN; }
"inference(" { return TOK_INFERENCE_PARENOPEN; }
"introduced(" { return TOK_INTRODUCED_PARENOPEN; }
"tcf(" { return TOK_TCF_PARENOPEN; }
"tff(" { return TOK_TFF_PARENOPEN; }
"theory(" { return TOK_THEORY_PARENOPEN; }
"thf(" { return TOK_THF_PARENOPEN; }
"tpi(" { return TOK_TPI_PARENOPEN; }
"unknown" { return TOK_UNKNOWN; }
"{" { return TOK_BRACEOPEN; }
"{.}" { return TOK_BRACEOPEN_DOT_BRACECLOSE; }
"}" { return TOK_BRACECLOSE; }
"~" { return TOK_TILDE; }
"~&" { return TOK_TILDE_AMPERSAND; }
"|" { return TOK_VLINE; }
">" { return TOK_ARROW; }
"<" { return TOK_LESS_SIGN; }
"*" { return TOK_STAR; }
"+" { return TOK_PLUS; }
"#" { return TOK_HASH; }

{single_quoted} { yylval->raw = strndup(yytext + 1, strlen(yytext) - 2); return TOK_SINGLE_QUOTED; }
{back_quoted} { yylval->raw = strdup(yytext + 1); return TOK_BACK_QUOTED; }
{distinct_object} { yylval->raw = strndup(yytext + 1, strlen(yytext) - 2); return TOK_DISTINCT_OBJECT; }
{dollar_word} { yylval->raw = strdup(yytext + 1); return TOK_DOLLAR_WORD; }
{dollar_dollar_word} { yylval->raw = strdup(yytext + 2); return TOK_DOLLAR_DOLLAR_WORD; }
{upper_word} { yylval->raw = strdup(yytext); return TOK_UPPER_WORD; }
{lower_word} { yylval->raw = strdup(yytext); return TOK_LOWER_WORD; }
{real} { yylval->raw = strdup(yytext); return TOK_REAL; }
{rational} { yylval->raw = strdup(yytext); return TOK_RATIONAL; }
{integer} { yylval->raw = strdup(yytext); return TOK_INTEGER; }

<<EOF>> { yyterminate(); }

. { yyextra->error = true; }

%%

/* Buffer only the formula of a fof record. Vampire's FOOL extension needs
 * the TFF grammar for formula-valued $ite arguments. Tokens are scanned once;
 * no text is copied or rewritten, and TFF/THF proofs take the direct path.
 * Quoted names, comments and annotations cannot trigger promotion. */
typedef struct TptpLexToken {
  int kind;
  YYSTYPE value;
} TptpLexToken;

static bool raw_token(int kind) {
  switch (kind) {
    case TOK_SINGLE_QUOTED: case TOK_BACK_QUOTED: case TOK_DISTINCT_OBJECT:
    case TOK_DOLLAR_WORD: case TOK_DOLLAR_DOLLAR_WORD: case TOK_UPPER_WORD:
    case TOK_LOWER_WORD: case TOK_REAL: case TOK_RATIONAL: case TOK_INTEGER:
      return true;
    default: return false;
  }
}

void tptp_lexer_cleanup(yyscan_t scanner) {
  TptpParseContext *context = yyget_extra(scanner);
  for (size_t i = context->token_next; i < context->token_count; ++i) {
    if (raw_token(context->tokens[i].kind)) free(context->tokens[i].value.raw);
  }
  free(context->tokens);
  context->tokens = NULL;
  context->token_count = context->token_next = 0;
}

int yylex(YYSTYPE *value, yyscan_t scanner) {
  TptpParseContext *context = yyget_extra(scanner);
  if (context->token_next < context->token_count) {
    TptpLexToken token = context->tokens[context->token_next++];
    *value = token.value;
    return token.kind;
  }
  tptp_lexer_cleanup(scanner);
  int kind = tptp_lex(value, scanner);
  if (kind != TOK_FOF_PARENOPEN) return kind;

  size_t capacity = 0;
  int depth = 1, brackets = 0, commas = 0;
  bool conditional = false, previous_ite = false;
  for (;;) {
    YYSTYPE next = {0};
    int token = tptp_lex(&next, scanner);
    if (context->token_count == capacity) {
      size_t grown = capacity ? capacity * 2 : 64;
      TptpLexToken *buffer = realloc(context->tokens, grown * sizeof(*buffer));
      if (!buffer) {
        if (raw_token(token)) free(next.raw);
        context->error = true;
        return 0;
      }
      context->tokens = buffer;
      capacity = grown;
    }
    context->tokens[context->token_count++] = (TptpLexToken){token, next};
    if (commas == 2 && previous_ite && token == TOK_PARENOPEN) conditional = true;
    previous_ite = token == TOK_DOLLAR_WORD && strcmp(next.raw, "ite") == 0;
    switch (token) {
      case TOK_PARENOPEN: case TOK_DOLLAR_LET_PARENOPEN:
      case TOK_DOLLAR_CNF_PARENOPEN: case TOK_DOLLAR_FOF_PARENOPEN:
      case TOK_DOLLAR_FOT_PARENOPEN: case TOK_DOLLAR_TFF_PARENOPEN:
      case TOK_DOLLAR_THF_PARENOPEN:
        ++depth; break;
      case TOK_PARENCLOSE: --depth; break;
      case TOK_BRACKOPEN: ++brackets; break;
      case TOK_BRACKCLOSE: --brackets; break;
      case TOK_COMMA:
        if (depth == 1 && brackets == 0) ++commas;
        break;
      default: break;
    }
    if (!token || token == TOK_PLOSE_DOT || commas == 3) break;
  }
  return conditional ? TOK_TFF_PARENOPEN : TOK_FOF_PARENOPEN;
}
