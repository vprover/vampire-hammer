/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_PARSER_TAB_H_INCLUDED
# define YY_YY_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif
/* "%code requires" blocks.  */
#line 67 "parser.y"

  #include <stdbool.h>
  #include <stdio.h>
  #include <lean/lean.h>

  #ifndef YY_TYPEDEF_YY_SCANNER_T
  #define YY_TYPEDEF_YY_SCANNER_T
  typedef void *yyscan_t;
  #endif

  typedef struct {
    bool error;
    lean_object *result;
    /* Lookahead is needed only for Vampire FOF records containing FOOL. */
    struct TptpLexToken *tokens;
    size_t token_count, token_next;
  } TptpParseContext;

#line 68 "parser.tab.h"

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    TOK_YYEMPTY = -2,
    TOK_YYEOF = 0,                 /* "end of file"  */
    TOK_YYerror = 256,             /* error  */
    TOK_YYUNDEF = 257,             /* "invalid token"  */
    TOK_SINGLE_QUOTED = 258,       /* SINGLE_QUOTED  */
    TOK_BACK_QUOTED = 259,         /* BACK_QUOTED  */
    TOK_DISTINCT_OBJECT = 260,     /* DISTINCT_OBJECT  */
    TOK_DOLLAR_WORD = 261,         /* DOLLAR_WORD  */
    TOK_DOLLAR_DOLLAR_WORD = 262,  /* DOLLAR_DOLLAR_WORD  */
    TOK_UPPER_WORD = 263,          /* UPPER_WORD  */
    TOK_LOWER_WORD = 264,          /* LOWER_WORD  */
    TOK_REAL = 265,                /* REAL  */
    TOK_RATIONAL = 266,            /* RATIONAL  */
    TOK_INTEGER = 267,             /* INTEGER  */
    TOK_EXCLAMATION = 268,         /* "!"  */
    TOK_DOUBLE_EXCLAMATION = 269,  /* "!!"  */
    TOK_EXCLAMATION_EQUALS = 270,  /* "!="  */
    TOK_EXCLAMATION_ARROW = 271,   /* "!>"  */
    TOK_DOLLAR_CNF_PARENOPEN = 272, /* "$cnf("  */
    TOK_DOLLAR_FOF_PARENOPEN = 273, /* "$fof("  */
    TOK_DOLLAR_FOT_PARENOPEN = 274, /* "$fot("  */
    TOK_DOLLAR_LET_PARENOPEN = 275, /* "$let("  */
    TOK_DOLLAR_TFF_PARENOPEN = 276, /* "$tff("  */
    TOK_DOLLAR_THF_PARENOPEN = 277, /* "$thf("  */
    TOK_AMPERSAND = 278,           /* "&"  */
    TOK_PARENOPEN = 279,           /* "("  */
    TOK_PARENOPEN_DOT_PARENCLOSE = 280, /* "(.)"  */
    TOK_PARENCLOSE = 281,          /* ")"  */
    TOK_PLOSE_DOT = 282,           /* ")."  */
    TOK_PARENCLOSE_BRACECLOSE = 283, /* ")}"  */
    TOK_COMMA = 284,               /* ","  */
    TOK_HYPEN = 285,               /* "-"  */
    TOK_DOUBLE_HYPHEN_ARROW = 286, /* "-->"  */
    TOK_DOT = 287,                 /* "."  */
    TOK_COLON = 288,               /* ":"  */
    TOK_COLOR_EQUALS = 289,        /* ":="  */
    TOK_DOUBLE_LESS_SIGN = 290,    /* "<<"  */
    TOK_LESS_SIGN_EQUALS = 291,    /* "<="  */
    TOK_LESS_SIGN_EQUALS_ARROW = 292, /* "<=>"  */
    TOK_LESS_SIGN_TILDE_ARROW = 293, /* "<~>"  */
    TOK_EQUALS = 294,              /* "="  */
    TOK_DOUBLE_EQUALS = 295,       /* "=="  */
    TOK_EQUALS_ARROW = 296,        /* "=>"  */
    TOK_QUESTION = 297,            /* "?"  */
    TOK_QUESTION_STAR = 298,       /* "?*"  */
    TOK_DOUBLE_QUESTION = 299,     /* "??"  */
    TOK_AT = 300,                  /* "@"  */
    TOK_AT_PLUS = 301,             /* "@+"  */
    TOK_AT_MINUS = 302,            /* "@-"  */
    TOK_AT_EQUALS = 303,           /* "@="  */
    TOK_DOUBLE_AT_PLUS = 304,      /* "@@+"  */
    TOK_DOUBLE_AT_MINUS = 305,     /* "@@-"  */
    TOK_BRACKOPEN = 306,           /* "["  */
    TOK_BRACKOPEN_DOT_BRACKCLOSE = 307, /* "[.]"  */
    TOK_BRACKOPEN_BRACKCLOSE = 308, /* "[]"  */
    TOK_BRACKCLOSE = 309,          /* "]"  */
    TOK_CARET = 310,               /* "^"  */
    TOK_CNF_PARENOPEN = 311,       /* "cnf("  */
    TOK_CREATOR_PARENOPEN = 312,   /* "creator("  */
    TOK_FILE_PARENOPEN = 313,      /* "file("  */
    TOK_FOF_PARENOPEN = 314,       /* "fof("  */
    TOK_INCLUDE_PARENOPEN = 315,   /* "include("  */
    TOK_INFERENCE_PARENOPEN = 316, /* "inference("  */
    TOK_INTRODUCED_PARENOPEN = 317, /* "introduced("  */
    TOK_TCF_PARENOPEN = 318,       /* "tcf("  */
    TOK_TFF_PARENOPEN = 319,       /* "tff("  */
    TOK_THEORY_PARENOPEN = 320,    /* "theory("  */
    TOK_THF_PARENOPEN = 321,       /* "thf("  */
    TOK_TPI_PARENOPEN = 322,       /* "tpi("  */
    TOK_UNKNOWN = 323,             /* "unknown"  */
    TOK_BRACEOPEN = 324,           /* "{"  */
    TOK_BRACEOPEN_DOT_BRACECLOSE = 325, /* "{.}"  */
    TOK_BRACECLOSE = 326,          /* "}"  */
    TOK_TILDE = 327,               /* "~"  */
    TOK_TILDE_AMPERSAND = 328,     /* "~&"  */
    TOK_VLINE = 329,               /* "|"  */
    TOK_ARROW = 330,               /* ">"  */
    TOK_LESS_SIGN = 331,           /* "<"  */
    TOK_STAR = 332,                /* "*"  */
    TOK_PLUS = 333,                /* "+"  */
    TOK_HASH = 334                 /* "#"  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 101 "parser.y"

  char *raw;
  lean_object *data;

#line 169 "parser.tab.h"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif




int yyparse (yyscan_t scanner, TptpParseContext *context);

/* "%code provides" blocks.  */
#line 86 "parser.y"

  int yylex(YYSTYPE *value, yyscan_t scanner);
  int yylex_init_extra(TptpParseContext *context, yyscan_t *scanner);
  int yylex_destroy(yyscan_t scanner);
  void tptp_lexer_cleanup(yyscan_t scanner);
  void yyset_in(FILE *input, yyscan_t scanner);
  void yyerror(yyscan_t scanner, TptpParseContext *context, const char *message);

#line 192 "parser.tab.h"

#endif /* !YY_YY_PARSER_TAB_H_INCLUDED  */
