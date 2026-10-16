/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 2

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* First part of user prologue.  */
#line 1 "parser.y"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

#include "extern_defs.h"

#define YYMAXDEPTH 1000000

/* Lean's C conversion accepts a minus sign but not TPTP's optional plus. */
static lean_object *parse_integer(const char *text) {
  return lean_cstr_to_int(text + (text[0] == '+'));
}

lean_object * parse_rational(const char *s_input) {
  char *s = strdup(s_input);

  char *slash_pos = strchr(s, '/');

  lean_object * n;
  lean_object * d;

  if (slash_pos) {
    slash_pos[0] = '\0';
    n = parse_integer(s);
    d = lean_cstr_to_nat(slash_pos + 1);
  } else {
    n = parse_integer(s);
    d = lean_usize_to_nat(1);
  }

  free(s);

  return Tptp_mk_Rational_mk(n, d);
}

lean_object * parse_real(const char *s_input) {
  char *s = strdup(s_input);
  char *exponent_pos = strpbrk(s, "eE");
  /* Read the exponent before removing the decimal point: moving the
   * mantissa shifts the old exponent pointer into the exponent itself. */
  lean_object *decimal_exponent = exponent_pos
    ? parse_integer(exponent_pos + 1) : lean_isize_to_int(0);
  if (exponent_pos) *exponent_pos = '\0';

  char *dot_pos = strchr(s, '.');
  if (dot_pos) {
    size_t fractional_digits = strlen(dot_pos + 1);
    memmove(dot_pos, dot_pos + 1, fractional_digits + 1);
    lean_object *offset = lean_nat_to_int(lean_usize_to_nat(fractional_digits));
    lean_object *adjusted = lean_int_sub(decimal_exponent, offset);
    lean_dec(decimal_exponent);
    lean_dec(offset);
    decimal_exponent = adjusted;
  }
  lean_object *mantisse = parse_integer(s);
  free(s);
  return Tptp_mk_Real_mk(mantisse, decimal_exponent);
}


#line 136 "parser.tab.c"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "parser.tab.h"
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_SINGLE_QUOTED = 3,              /* SINGLE_QUOTED  */
  YYSYMBOL_BACK_QUOTED = 4,                /* BACK_QUOTED  */
  YYSYMBOL_DISTINCT_OBJECT = 5,            /* DISTINCT_OBJECT  */
  YYSYMBOL_DOLLAR_WORD = 6,                /* DOLLAR_WORD  */
  YYSYMBOL_DOLLAR_DOLLAR_WORD = 7,         /* DOLLAR_DOLLAR_WORD  */
  YYSYMBOL_UPPER_WORD = 8,                 /* UPPER_WORD  */
  YYSYMBOL_LOWER_WORD = 9,                 /* LOWER_WORD  */
  YYSYMBOL_REAL = 10,                      /* REAL  */
  YYSYMBOL_RATIONAL = 11,                  /* RATIONAL  */
  YYSYMBOL_INTEGER = 12,                   /* INTEGER  */
  YYSYMBOL_EXCLAMATION = 13,               /* "!"  */
  YYSYMBOL_DOUBLE_EXCLAMATION = 14,        /* "!!"  */
  YYSYMBOL_EXCLAMATION_EQUALS = 15,        /* "!="  */
  YYSYMBOL_EXCLAMATION_ARROW = 16,         /* "!>"  */
  YYSYMBOL_DOLLAR_CNF_PARENOPEN = 17,      /* "$cnf("  */
  YYSYMBOL_DOLLAR_FOF_PARENOPEN = 18,      /* "$fof("  */
  YYSYMBOL_DOLLAR_FOT_PARENOPEN = 19,      /* "$fot("  */
  YYSYMBOL_DOLLAR_LET_PARENOPEN = 20,      /* "$let("  */
  YYSYMBOL_DOLLAR_TFF_PARENOPEN = 21,      /* "$tff("  */
  YYSYMBOL_DOLLAR_THF_PARENOPEN = 22,      /* "$thf("  */
  YYSYMBOL_AMPERSAND = 23,                 /* "&"  */
  YYSYMBOL_PARENOPEN = 24,                 /* "("  */
  YYSYMBOL_PARENOPEN_DOT_PARENCLOSE = 25,  /* "(.)"  */
  YYSYMBOL_PARENCLOSE = 26,                /* ")"  */
  YYSYMBOL_PLOSE_DOT = 27,                 /* ")."  */
  YYSYMBOL_PARENCLOSE_BRACECLOSE = 28,     /* ")}"  */
  YYSYMBOL_COMMA = 29,                     /* ","  */
  YYSYMBOL_HYPEN = 30,                     /* "-"  */
  YYSYMBOL_DOUBLE_HYPHEN_ARROW = 31,       /* "-->"  */
  YYSYMBOL_DOT = 32,                       /* "."  */
  YYSYMBOL_COLON = 33,                     /* ":"  */
  YYSYMBOL_COLOR_EQUALS = 34,              /* ":="  */
  YYSYMBOL_DOUBLE_LESS_SIGN = 35,          /* "<<"  */
  YYSYMBOL_LESS_SIGN_EQUALS = 36,          /* "<="  */
  YYSYMBOL_LESS_SIGN_EQUALS_ARROW = 37,    /* "<=>"  */
  YYSYMBOL_LESS_SIGN_TILDE_ARROW = 38,     /* "<~>"  */
  YYSYMBOL_EQUALS = 39,                    /* "="  */
  YYSYMBOL_DOUBLE_EQUALS = 40,             /* "=="  */
  YYSYMBOL_EQUALS_ARROW = 41,              /* "=>"  */
  YYSYMBOL_QUESTION = 42,                  /* "?"  */
  YYSYMBOL_QUESTION_STAR = 43,             /* "?*"  */
  YYSYMBOL_DOUBLE_QUESTION = 44,           /* "??"  */
  YYSYMBOL_AT = 45,                        /* "@"  */
  YYSYMBOL_AT_PLUS = 46,                   /* "@+"  */
  YYSYMBOL_AT_MINUS = 47,                  /* "@-"  */
  YYSYMBOL_AT_EQUALS = 48,                 /* "@="  */
  YYSYMBOL_DOUBLE_AT_PLUS = 49,            /* "@@+"  */
  YYSYMBOL_DOUBLE_AT_MINUS = 50,           /* "@@-"  */
  YYSYMBOL_BRACKOPEN = 51,                 /* "["  */
  YYSYMBOL_BRACKOPEN_DOT_BRACKCLOSE = 52,  /* "[.]"  */
  YYSYMBOL_BRACKOPEN_BRACKCLOSE = 53,      /* "[]"  */
  YYSYMBOL_BRACKCLOSE = 54,                /* "]"  */
  YYSYMBOL_CARET = 55,                     /* "^"  */
  YYSYMBOL_CNF_PARENOPEN = 56,             /* "cnf("  */
  YYSYMBOL_CREATOR_PARENOPEN = 57,         /* "creator("  */
  YYSYMBOL_FILE_PARENOPEN = 58,            /* "file("  */
  YYSYMBOL_FOF_PARENOPEN = 59,             /* "fof("  */
  YYSYMBOL_INCLUDE_PARENOPEN = 60,         /* "include("  */
  YYSYMBOL_INFERENCE_PARENOPEN = 61,       /* "inference("  */
  YYSYMBOL_INTRODUCED_PARENOPEN = 62,      /* "introduced("  */
  YYSYMBOL_TCF_PARENOPEN = 63,             /* "tcf("  */
  YYSYMBOL_TFF_PARENOPEN = 64,             /* "tff("  */
  YYSYMBOL_THEORY_PARENOPEN = 65,          /* "theory("  */
  YYSYMBOL_THF_PARENOPEN = 66,             /* "thf("  */
  YYSYMBOL_TPI_PARENOPEN = 67,             /* "tpi("  */
  YYSYMBOL_UNKNOWN = 68,                   /* "unknown"  */
  YYSYMBOL_BRACEOPEN = 69,                 /* "{"  */
  YYSYMBOL_BRACEOPEN_DOT_BRACECLOSE = 70,  /* "{.}"  */
  YYSYMBOL_BRACECLOSE = 71,                /* "}"  */
  YYSYMBOL_TILDE = 72,                     /* "~"  */
  YYSYMBOL_TILDE_AMPERSAND = 73,           /* "~&"  */
  YYSYMBOL_VLINE = 74,                     /* "|"  */
  YYSYMBOL_ARROW = 75,                     /* ">"  */
  YYSYMBOL_LESS_SIGN = 76,                 /* "<"  */
  YYSYMBOL_STAR = 77,                      /* "*"  */
  YYSYMBOL_PLUS = 78,                      /* "+"  */
  YYSYMBOL_HASH = 79,                      /* "#"  */
  YYSYMBOL_YYACCEPT = 80,                  /* $accept  */
  YYSYMBOL_start = 81,                     /* start  */
  YYSYMBOL_tptp_file = 82,                 /* tptp_file  */
  YYSYMBOL_tptp_input_list = 83,           /* tptp_input_list  */
  YYSYMBOL_tptp_input = 84,                /* tptp_input  */
  YYSYMBOL_annotated_formula = 85,         /* annotated_formula  */
  YYSYMBOL_tpi_annotated = 86,             /* tpi_annotated  */
  YYSYMBOL_tpi_formula = 87,               /* tpi_formula  */
  YYSYMBOL_thf_annotated = 88,             /* thf_annotated  */
  YYSYMBOL_tff_annotated = 89,             /* tff_annotated  */
  YYSYMBOL_tcf_annotated = 90,             /* tcf_annotated  */
  YYSYMBOL_fof_annotated = 91,             /* fof_annotated  */
  YYSYMBOL_cnf_annotated = 92,             /* cnf_annotated  */
  YYSYMBOL_annotations = 93,               /* annotations  */
  YYSYMBOL_formula_role = 94,              /* formula_role  */
  YYSYMBOL_thf_formula = 95,               /* thf_formula  */
  YYSYMBOL_thf_logic_formula = 96,         /* thf_logic_formula  */
  YYSYMBOL_thf_binary_formula = 97,        /* thf_binary_formula  */
  YYSYMBOL_thf_binary_nonassoc = 98,       /* thf_binary_nonassoc  */
  YYSYMBOL_thf_binary_assoc = 99,          /* thf_binary_assoc  */
  YYSYMBOL_thf_or_formula = 100,           /* thf_or_formula  */
  YYSYMBOL_thf_and_formula = 101,          /* thf_and_formula  */
  YYSYMBOL_thf_apply_formula = 102,        /* thf_apply_formula  */
  YYSYMBOL_thf_unit_formula = 103,         /* thf_unit_formula  */
  YYSYMBOL_thf_preunit_formula = 104,      /* thf_preunit_formula  */
  YYSYMBOL_thf_unitary_formula = 105,      /* thf_unitary_formula  */
  YYSYMBOL_thf_quantified_formula = 106,   /* thf_quantified_formula  */
  YYSYMBOL_thf_quantification = 107,       /* thf_quantification  */
  YYSYMBOL_thf_variable_list = 108,        /* thf_variable_list  */
  YYSYMBOL_thf_typed_variable = 109,       /* thf_typed_variable  */
  YYSYMBOL_thf_unary_formula = 110,        /* thf_unary_formula  */
  YYSYMBOL_thf_prefix_unary = 111,         /* thf_prefix_unary  */
  YYSYMBOL_thf_infix_unary = 112,          /* thf_infix_unary  */
  YYSYMBOL_thf_atomic_formula = 113,       /* thf_atomic_formula  */
  YYSYMBOL_thf_plain_atomic = 114,         /* thf_plain_atomic  */
  YYSYMBOL_thf_defined_atomic = 115,       /* thf_defined_atomic  */
  YYSYMBOL_thf_defined_term = 116,         /* thf_defined_term  */
  YYSYMBOL_thf_defined_infix = 117,        /* thf_defined_infix  */
  YYSYMBOL_thf_system_atomic = 118,        /* thf_system_atomic  */
  YYSYMBOL_thf_let = 119,                  /* thf_let  */
  YYSYMBOL_thf_let_types = 120,            /* thf_let_types  */
  YYSYMBOL_thf_atom_typing_list = 121,     /* thf_atom_typing_list  */
  YYSYMBOL_thf_let_defns = 122,            /* thf_let_defns  */
  YYSYMBOL_thf_let_defn = 123,             /* thf_let_defn  */
  YYSYMBOL_thf_let_defn_list = 124,        /* thf_let_defn_list  */
  YYSYMBOL_thf_unitary_term = 125,         /* thf_unitary_term  */
  YYSYMBOL_thf_conn_term = 126,            /* thf_conn_term  */
  YYSYMBOL_thf_tuple = 127,                /* thf_tuple  */
  YYSYMBOL_thf_fof_function = 128,         /* thf_fof_function  */
  YYSYMBOL_thf_arguments = 129,            /* thf_arguments  */
  YYSYMBOL_thf_formula_list = 130,         /* thf_formula_list  */
  YYSYMBOL_comma_thf_logic_formula_list = 131, /* comma_thf_logic_formula_list  */
  YYSYMBOL_comma_thf_logic_formula = 132,  /* comma_thf_logic_formula  */
  YYSYMBOL_thf_atom_typing = 133,          /* thf_atom_typing  */
  YYSYMBOL_thf_top_level_type = 134,       /* thf_top_level_type  */
  YYSYMBOL_thf_unitary_type = 135,         /* thf_unitary_type  */
  YYSYMBOL_thf_apply_type = 136,           /* thf_apply_type  */
  YYSYMBOL_thf_binary_type = 137,          /* thf_binary_type  */
  YYSYMBOL_thf_mapping_type = 138,         /* thf_mapping_type  */
  YYSYMBOL_thf_xprod_type = 139,           /* thf_xprod_type  */
  YYSYMBOL_thf_union_type = 140,           /* thf_union_type  */
  YYSYMBOL_thf_subtype = 141,              /* thf_subtype  */
  YYSYMBOL_thf_definition = 142,           /* thf_definition  */
  YYSYMBOL_thf_sequent = 143,              /* thf_sequent  */
  YYSYMBOL_tff_formula = 144,              /* tff_formula  */
  YYSYMBOL_tff_logic_formula = 145,        /* tff_logic_formula  */
  YYSYMBOL_tff_binary_formula = 146,       /* tff_binary_formula  */
  YYSYMBOL_tff_binary_nonassoc = 147,      /* tff_binary_nonassoc  */
  YYSYMBOL_tff_binary_assoc = 148,         /* tff_binary_assoc  */
  YYSYMBOL_tff_or_formula = 149,           /* tff_or_formula  */
  YYSYMBOL_tff_and_formula = 150,          /* tff_and_formula  */
  YYSYMBOL_tff_unit_formula = 151,         /* tff_unit_formula  */
  YYSYMBOL_tff_preunit_formula = 152,      /* tff_preunit_formula  */
  YYSYMBOL_tff_unitary_formula = 153,      /* tff_unitary_formula  */
  YYSYMBOL_txf_unitary_formula = 154,      /* txf_unitary_formula  */
  YYSYMBOL_tff_quantified_formula = 155,   /* tff_quantified_formula  */
  YYSYMBOL_tff_variable_list = 156,        /* tff_variable_list  */
  YYSYMBOL_tff_variable = 157,             /* tff_variable  */
  YYSYMBOL_tff_typed_variable = 158,       /* tff_typed_variable  */
  YYSYMBOL_tff_unary_formula = 159,        /* tff_unary_formula  */
  YYSYMBOL_tff_prefix_unary = 160,         /* tff_prefix_unary  */
  YYSYMBOL_tff_infix_unary = 161,          /* tff_infix_unary  */
  YYSYMBOL_tff_atomic_formula = 162,       /* tff_atomic_formula  */
  YYSYMBOL_tff_plain_atomic = 163,         /* tff_plain_atomic  */
  YYSYMBOL_tff_defined_atomic = 164,       /* tff_defined_atomic  */
  YYSYMBOL_tff_defined_plain = 165,        /* tff_defined_plain  */
  YYSYMBOL_tff_defined_infix = 166,        /* tff_defined_infix  */
  YYSYMBOL_tff_system_atomic = 167,        /* tff_system_atomic  */
  YYSYMBOL_txf_let = 168,                  /* txf_let  */
  YYSYMBOL_txf_let_types = 169,            /* txf_let_types  */
  YYSYMBOL_tff_atom_typing_list = 170,     /* tff_atom_typing_list  */
  YYSYMBOL_txf_let_defns = 171,            /* txf_let_defns  */
  YYSYMBOL_txf_let_defn = 172,             /* txf_let_defn  */
  YYSYMBOL_txf_let_LHS = 173,              /* txf_let_LHS  */
  YYSYMBOL_txf_let_defn_list = 174,        /* txf_let_defn_list  */
  YYSYMBOL_nxf_atom = 175,                 /* nxf_atom  */
  YYSYMBOL_tff_term = 176,                 /* tff_term  */
  YYSYMBOL_tff_unitary_term = 177,         /* tff_unitary_term  */
  YYSYMBOL_txf_tuple = 178,                /* txf_tuple  */
  YYSYMBOL_tff_arguments = 179,            /* tff_arguments  */
  YYSYMBOL_comma_tff_term_list = 180,      /* comma_tff_term_list  */
  YYSYMBOL_comma_tff_term = 181,           /* comma_tff_term  */
  YYSYMBOL_tff_atom_typing = 182,          /* tff_atom_typing  */
  YYSYMBOL_tff_top_level_type = 183,       /* tff_top_level_type  */
  YYSYMBOL_tff_non_atomic_type = 184,      /* tff_non_atomic_type  */
  YYSYMBOL_tf1_quantified_type = 185,      /* tf1_quantified_type  */
  YYSYMBOL_tff_monotype = 186,             /* tff_monotype  */
  YYSYMBOL_tff_unitary_type = 187,         /* tff_unitary_type  */
  YYSYMBOL_tff_atomic_type = 188,          /* tff_atomic_type  */
  YYSYMBOL_tff_type_arguments = 189,       /* tff_type_arguments  */
  YYSYMBOL_tff_mapping_type = 190,         /* tff_mapping_type  */
  YYSYMBOL_tff_xprod_type = 191,           /* tff_xprod_type  */
  YYSYMBOL_txf_tuple_type = 192,           /* txf_tuple_type  */
  YYSYMBOL_tff_type_list = 193,            /* tff_type_list  */
  YYSYMBOL_tff_subtype = 194,              /* tff_subtype  */
  YYSYMBOL_txf_definition = 195,           /* txf_definition  */
  YYSYMBOL_txf_sequent = 196,              /* txf_sequent  */
  YYSYMBOL_nhf_long_connective = 197,      /* nhf_long_connective  */
  YYSYMBOL_nhf_parameter_list = 198,       /* nhf_parameter_list  */
  YYSYMBOL_nhf_parameter = 199,            /* nhf_parameter  */
  YYSYMBOL_nhf_key_pair = 200,             /* nhf_key_pair  */
  YYSYMBOL_nxf_long_connective = 201,      /* nxf_long_connective  */
  YYSYMBOL_nxf_parameter_list = 202,       /* nxf_parameter_list  */
  YYSYMBOL_nxf_parameter = 203,            /* nxf_parameter  */
  YYSYMBOL_nxf_key_pair = 204,             /* nxf_key_pair  */
  YYSYMBOL_ntf_connective_name = 205,      /* ntf_connective_name  */
  YYSYMBOL_ntf_index = 206,                /* ntf_index  */
  YYSYMBOL_ntf_short_connective = 207,     /* ntf_short_connective  */
  YYSYMBOL_tcf_formula = 208,              /* tcf_formula  */
  YYSYMBOL_tcf_logic_formula = 209,        /* tcf_logic_formula  */
  YYSYMBOL_tcf_quantified_formula = 210,   /* tcf_quantified_formula  */
  YYSYMBOL_fof_formula = 211,              /* fof_formula  */
  YYSYMBOL_fof_logic_formula = 212,        /* fof_logic_formula  */
  YYSYMBOL_fof_binary_formula = 213,       /* fof_binary_formula  */
  YYSYMBOL_fof_binary_nonassoc = 214,      /* fof_binary_nonassoc  */
  YYSYMBOL_fof_binary_assoc = 215,         /* fof_binary_assoc  */
  YYSYMBOL_fof_or_formula = 216,           /* fof_or_formula  */
  YYSYMBOL_fof_and_formula = 217,          /* fof_and_formula  */
  YYSYMBOL_fof_unary_formula = 218,        /* fof_unary_formula  */
  YYSYMBOL_fof_infix_unary = 219,          /* fof_infix_unary  */
  YYSYMBOL_fof_unit_formula = 220,         /* fof_unit_formula  */
  YYSYMBOL_fof_unitary_formula = 221,      /* fof_unitary_formula  */
  YYSYMBOL_fof_quantified_formula = 222,   /* fof_quantified_formula  */
  YYSYMBOL_fof_variable_list = 223,        /* fof_variable_list  */
  YYSYMBOL_fof_atomic_formula = 224,       /* fof_atomic_formula  */
  YYSYMBOL_fof_plain_atomic_formula = 225, /* fof_plain_atomic_formula  */
  YYSYMBOL_fof_defined_atomic_formula = 226, /* fof_defined_atomic_formula  */
  YYSYMBOL_fof_defined_plain_formula = 227, /* fof_defined_plain_formula  */
  YYSYMBOL_fof_defined_infix_formula = 228, /* fof_defined_infix_formula  */
  YYSYMBOL_fof_system_atomic_formula = 229, /* fof_system_atomic_formula  */
  YYSYMBOL_fof_plain_term = 230,           /* fof_plain_term  */
  YYSYMBOL_fof_defined_term = 231,         /* fof_defined_term  */
  YYSYMBOL_fof_defined_atomic_term = 232,  /* fof_defined_atomic_term  */
  YYSYMBOL_fof_defined_plain_term = 233,   /* fof_defined_plain_term  */
  YYSYMBOL_fof_system_term = 234,          /* fof_system_term  */
  YYSYMBOL_fof_arguments = 235,            /* fof_arguments  */
  YYSYMBOL_fof_term = 236,                 /* fof_term  */
  YYSYMBOL_fof_function_term = 237,        /* fof_function_term  */
  YYSYMBOL_fof_sequent = 238,              /* fof_sequent  */
  YYSYMBOL_fof_formula_tuple = 239,        /* fof_formula_tuple  */
  YYSYMBOL_fof_formula_tuple_list = 240,   /* fof_formula_tuple_list  */
  YYSYMBOL_comma_fof_logic_formula_list = 241, /* comma_fof_logic_formula_list  */
  YYSYMBOL_comma_fof_logic_formula = 242,  /* comma_fof_logic_formula  */
  YYSYMBOL_cnf_formula = 243,              /* cnf_formula  */
  YYSYMBOL_cnf_disjunction = 244,          /* cnf_disjunction  */
  YYSYMBOL_cnf_literal = 245,              /* cnf_literal  */
  YYSYMBOL_thf_quantifier = 246,           /* thf_quantifier  */
  YYSYMBOL_thf_unary_connective = 247,     /* thf_unary_connective  */
  YYSYMBOL_th0_quantifier = 248,           /* th0_quantifier  */
  YYSYMBOL_type_quantifier = 249,          /* type_quantifier  */
  YYSYMBOL_subtype_sign = 250,             /* subtype_sign  */
  YYSYMBOL_tff_unary_connective = 251,     /* tff_unary_connective  */
  YYSYMBOL_tff_quantifier = 252,           /* tff_quantifier  */
  YYSYMBOL_fof_quantifier = 253,           /* fof_quantifier  */
  YYSYMBOL_nonassoc_connective = 254,      /* nonassoc_connective  */
  YYSYMBOL_assoc_connective = 255,         /* assoc_connective  */
  YYSYMBOL_unary_connective = 256,         /* unary_connective  */
  YYSYMBOL_gentzen_arrow = 257,            /* gentzen_arrow  */
  YYSYMBOL_assignment = 258,               /* assignment  */
  YYSYMBOL_identical = 259,                /* identical  */
  YYSYMBOL_type_constant = 260,            /* type_constant  */
  YYSYMBOL_type_functor = 261,             /* type_functor  */
  YYSYMBOL_defined_type = 262,             /* defined_type  */
  YYSYMBOL_atom = 263,                     /* atom  */
  YYSYMBOL_untyped_atom = 264,             /* untyped_atom  */
  YYSYMBOL_defined_infix_pred = 265,       /* defined_infix_pred  */
  YYSYMBOL_infix_equality = 266,           /* infix_equality  */
  YYSYMBOL_infix_inequality = 267,         /* infix_inequality  */
  YYSYMBOL_constant = 268,                 /* constant  */
  YYSYMBOL_functor = 269,                  /* functor  */
  YYSYMBOL_defined_constant = 270,         /* defined_constant  */
  YYSYMBOL_defined_functor = 271,          /* defined_functor  */
  YYSYMBOL_system_constant = 272,          /* system_constant  */
  YYSYMBOL_system_functor = 273,           /* system_functor  */
  YYSYMBOL_def_or_sys_constant = 274,      /* def_or_sys_constant  */
  YYSYMBOL_th1_defined_term = 275,         /* th1_defined_term  */
  YYSYMBOL_distinct_object = 276,          /* distinct_object  */
  YYSYMBOL_defined_term = 277,             /* defined_term  */
  YYSYMBOL_upper_word = 278,               /* upper_word  */
  YYSYMBOL_variable = 279,                 /* variable  */
  YYSYMBOL_source = 280,                   /* source  */
  YYSYMBOL_sources = 281,                  /* sources  */
  YYSYMBOL_dag_source = 282,               /* dag_source  */
  YYSYMBOL_inference_record = 283,         /* inference_record  */
  YYSYMBOL_inference_rule = 284,           /* inference_rule  */
  YYSYMBOL_internal_source = 285,          /* internal_source  */
  YYSYMBOL_intro_type = 286,               /* intro_type  */
  YYSYMBOL_external_source = 287,          /* external_source  */
  YYSYMBOL_file_source = 288,              /* file_source  */
  YYSYMBOL_file_info = 289,                /* file_info  */
  YYSYMBOL_theory = 290,                   /* theory  */
  YYSYMBOL_theory_name = 291,              /* theory_name  */
  YYSYMBOL_creator_source = 292,           /* creator_source  */
  YYSYMBOL_creator_name = 293,             /* creator_name  */
  YYSYMBOL_parents = 294,                  /* parents  */
  YYSYMBOL_parent_list = 295,              /* parent_list  */
  YYSYMBOL_comma_parent_info_list = 296,   /* comma_parent_info_list  */
  YYSYMBOL_comma_parent_info = 297,        /* comma_parent_info  */
  YYSYMBOL_parent_info = 298,              /* parent_info  */
  YYSYMBOL_parent_details = 299,           /* parent_details  */
  YYSYMBOL_optional_info = 300,            /* optional_info  */
  YYSYMBOL_useful_info = 301,              /* useful_info  */
  YYSYMBOL_include = 302,                  /* include  */
  YYSYMBOL_include_optionals = 303,        /* include_optionals  */
  YYSYMBOL_formula_selection = 304,        /* formula_selection  */
  YYSYMBOL_name_list = 305,                /* name_list  */
  YYSYMBOL_space_name = 306,               /* space_name  */
  YYSYMBOL_general_term = 307,             /* general_term  */
  YYSYMBOL_general_data = 308,             /* general_data  */
  YYSYMBOL_general_function = 309,         /* general_function  */
  YYSYMBOL_formula_data = 310,             /* formula_data  */
  YYSYMBOL_general_list = 311,             /* general_list  */
  YYSYMBOL_general_terms = 312,            /* general_terms  */
  YYSYMBOL_comma_general_term_list = 313,  /* comma_general_term_list  */
  YYSYMBOL_comma_general_term = 314,       /* comma_general_term  */
  YYSYMBOL_name = 315,                     /* name  */
  YYSYMBOL_lower_word = 316,               /* lower_word  */
  YYSYMBOL_single_quoted = 317,            /* single_quoted  */
  YYSYMBOL_back_quoted = 318,              /* back_quoted  */
  YYSYMBOL_atomic_word = 319,              /* atomic_word  */
  YYSYMBOL_dollar_word = 320,              /* dollar_word  */
  YYSYMBOL_dollar_dollar_word = 321,       /* dollar_dollar_word  */
  YYSYMBOL_atomic_defined_word = 322,      /* atomic_defined_word  */
  YYSYMBOL_atomic_system_word = 323,       /* atomic_system_word  */
  YYSYMBOL_integer = 324,                  /* integer  */
  YYSYMBOL_rational = 325,                 /* rational  */
  YYSYMBOL_real = 326,                     /* real  */
  YYSYMBOL_number = 327,                   /* number  */
  YYSYMBOL_file_name = 328                 /* file_name  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_int16 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if !defined yyoverflow

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* !defined yyoverflow */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  4
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   3147

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  80
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  249
/* YYNRULES -- Number of rules.  */
#define YYNRULES  472
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  812

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   334


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   441,   441,   445,   449,   450,   454,   455,   459,   460,
     461,   462,   463,   464,   468,   472,   476,   480,   484,   488,
     492,   496,   497,   501,   502,   506,   507,   508,   512,   513,
     514,   515,   516,   517,   521,   522,   523,   527,   531,   532,
     533,   537,   538,   542,   543,   549,   557,   558,   562,   563,
     564,   569,   574,   580,   581,   585,   586,   587,   588,   592,
     596,   600,   601,   605,   609,   610,   614,   618,   622,   623,
     624,   625,   629,   630,   634,   635,   636,   637,   638,   642,
     643,   647,   651,   655,   659,   660,   664,   665,   669,   670,
     674,   678,   679,   683,   684,   685,   689,   690,   691,   692,
     693,   697,   698,   702,   703,   704,   708,   712,   716,   717,
     721,   725,   726,   730,   731,   732,   736,   740,   744,   745,
     746,   750,   751,   755,   756,   760,   761,   765,   769,   773,
     777,   778,   779,   783,   784,   785,   786,   787,   788,   792,
     793,   797,   801,   802,   806,   807,   811,   812,   816,   817,
     818,   823,   828,   834,   835,   839,   840,   841,   842,   846,
     850,   854,   855,   859,   860,   864,   868,   869,   873,   877,
     881,   882,   883,   887,   888,   892,   896,   897,   898,   899,
     903,   907,   908,   912,   916,   917,   921,   922,   926,   927,
     931,   935,   936,   940,   941,   945,   949,   950,   951,   955,
     956,   957,   958,   959,   963,   964,   968,   972,   973,   977,
     981,   982,   986,   987,   991,   992,   993,   997,  1001,  1002,
    1003,  1007,  1008,  1012,  1013,  1014,  1015,  1016,  1017,  1021,
    1022,  1026,  1030,  1031,  1035,  1039,  1040,  1044,  1048,  1052,
    1056,  1057,  1061,  1062,  1066,  1067,  1071,  1075,  1076,  1080,
    1081,  1085,  1086,  1090,  1094,  1098,  1102,  1103,  1104,  1105,
    1109,  1110,  1114,  1115,  1119,  1123,  1124,  1128,  1129,  1130,
    1134,  1135,  1139,  1143,  1144,  1148,  1149,  1153,  1154,  1158,
    1159,  1163,  1167,  1168,  1172,  1173,  1174,  1178,  1182,  1183,
    1187,  1188,  1189,  1193,  1197,  1198,  1202,  1206,  1210,  1214,
    1215,  1219,  1220,  1224,  1228,  1229,  1233,  1234,  1238,  1239,
    1243,  1244,  1248,  1249,  1250,  1254,  1255,  1259,  1260,  1264,
    1268,  1269,  1273,  1277,  1278,  1282,  1283,  1287,  1288,  1289,
    1290,  1294,  1295,  1296,  1300,  1301,  1305,  1306,  1307,  1311,
    1312,  1316,  1320,  1321,  1325,  1326,  1330,  1331,  1335,  1336,
    1337,  1338,  1339,  1340,  1344,  1345,  1349,  1353,  1357,  1361,
    1365,  1369,  1373,  1377,  1378,  1382,  1383,  1387,  1391,  1395,
    1399,  1403,  1407,  1411,  1415,  1419,  1423,  1424,  1428,  1429,
    1430,  1431,  1432,  1436,  1440,  1441,  1445,  1449,  1454,  1455,
    1456,  1457,  1458,  1462,  1463,  1467,  1468,  1472,  1476,  1480,
    1484,  1488,  1489,  1490,  1494,  1498,  1499,  1503,  1507,  1511,
    1515,  1519,  1520,  1524,  1528,  1529,  1533,  1537,  1541,  1542,
    1546,  1547,  1551,  1555,  1559,  1560,  1561,  1565,  1566,  1570,
    1571,  1575,  1579,  1580,  1581,  1585,  1586,  1587,  1588,  1589,
    1590,  1594,  1598,  1599,  1600,  1601,  1602,  1606,  1607,  1611,
    1615,  1616,  1620,  1624,  1625,  1629,  1630,  1634,  1638,  1642,
    1643,  1644,  1648,  1652,  1656,  1660,  1664,  1668,  1672,  1676,
    1677,  1678,  1682
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if YYDEBUG || 0
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "SINGLE_QUOTED",
  "BACK_QUOTED", "DISTINCT_OBJECT", "DOLLAR_WORD", "DOLLAR_DOLLAR_WORD",
  "UPPER_WORD", "LOWER_WORD", "REAL", "RATIONAL", "INTEGER", "\"!\"",
  "\"!!\"", "\"!=\"", "\"!>\"", "\"$cnf(\"", "\"$fof(\"", "\"$fot(\"",
  "\"$let(\"", "\"$tff(\"", "\"$thf(\"", "\"&\"", "\"(\"", "\"(.)\"",
  "\")\"", "\").\"", "\")}\"", "\",\"", "\"-\"", "\"-->\"", "\".\"",
  "\":\"", "\":=\"", "\"<<\"", "\"<=\"", "\"<=>\"", "\"<~>\"", "\"=\"",
  "\"==\"", "\"=>\"", "\"?\"", "\"?*\"", "\"??\"", "\"@\"", "\"@+\"",
  "\"@-\"", "\"@=\"", "\"@@+\"", "\"@@-\"", "\"[\"", "\"[.]\"", "\"[]\"",
  "\"]\"", "\"^\"", "\"cnf(\"", "\"creator(\"", "\"file(\"", "\"fof(\"",
  "\"include(\"", "\"inference(\"", "\"introduced(\"", "\"tcf(\"",
  "\"tff(\"", "\"theory(\"", "\"thf(\"", "\"tpi(\"", "\"unknown\"",
  "\"{\"", "\"{.}\"", "\"}\"", "\"~\"", "\"~&\"", "\"|\"", "\">\"",
  "\"<\"", "\"*\"", "\"+\"", "\"#\"", "$accept", "start", "tptp_file",
  "tptp_input_list", "tptp_input", "annotated_formula", "tpi_annotated",
  "tpi_formula", "thf_annotated", "tff_annotated", "tcf_annotated",
  "fof_annotated", "cnf_annotated", "annotations", "formula_role",
  "thf_formula", "thf_logic_formula", "thf_binary_formula",
  "thf_binary_nonassoc", "thf_binary_assoc", "thf_or_formula",
  "thf_and_formula", "thf_apply_formula", "thf_unit_formula",
  "thf_preunit_formula", "thf_unitary_formula", "thf_quantified_formula",
  "thf_quantification", "thf_variable_list", "thf_typed_variable",
  "thf_unary_formula", "thf_prefix_unary", "thf_infix_unary",
  "thf_atomic_formula", "thf_plain_atomic", "thf_defined_atomic",
  "thf_defined_term", "thf_defined_infix", "thf_system_atomic", "thf_let",
  "thf_let_types", "thf_atom_typing_list", "thf_let_defns", "thf_let_defn",
  "thf_let_defn_list", "thf_unitary_term", "thf_conn_term", "thf_tuple",
  "thf_fof_function", "thf_arguments", "thf_formula_list",
  "comma_thf_logic_formula_list", "comma_thf_logic_formula",
  "thf_atom_typing", "thf_top_level_type", "thf_unitary_type",
  "thf_apply_type", "thf_binary_type", "thf_mapping_type",
  "thf_xprod_type", "thf_union_type", "thf_subtype", "thf_definition",
  "thf_sequent", "tff_formula", "tff_logic_formula", "tff_binary_formula",
  "tff_binary_nonassoc", "tff_binary_assoc", "tff_or_formula",
  "tff_and_formula", "tff_unit_formula", "tff_preunit_formula",
  "tff_unitary_formula", "txf_unitary_formula", "tff_quantified_formula",
  "tff_variable_list", "tff_variable", "tff_typed_variable",
  "tff_unary_formula", "tff_prefix_unary", "tff_infix_unary",
  "tff_atomic_formula", "tff_plain_atomic", "tff_defined_atomic",
  "tff_defined_plain", "tff_defined_infix", "tff_system_atomic", "txf_let",
  "txf_let_types", "tff_atom_typing_list", "txf_let_defns", "txf_let_defn",
  "txf_let_LHS", "txf_let_defn_list", "nxf_atom", "tff_term",
  "tff_unitary_term", "txf_tuple", "tff_arguments", "comma_tff_term_list",
  "comma_tff_term", "tff_atom_typing", "tff_top_level_type",
  "tff_non_atomic_type", "tf1_quantified_type", "tff_monotype",
  "tff_unitary_type", "tff_atomic_type", "tff_type_arguments",
  "tff_mapping_type", "tff_xprod_type", "txf_tuple_type", "tff_type_list",
  "tff_subtype", "txf_definition", "txf_sequent", "nhf_long_connective",
  "nhf_parameter_list", "nhf_parameter", "nhf_key_pair",
  "nxf_long_connective", "nxf_parameter_list", "nxf_parameter",
  "nxf_key_pair", "ntf_connective_name", "ntf_index",
  "ntf_short_connective", "tcf_formula", "tcf_logic_formula",
  "tcf_quantified_formula", "fof_formula", "fof_logic_formula",
  "fof_binary_formula", "fof_binary_nonassoc", "fof_binary_assoc",
  "fof_or_formula", "fof_and_formula", "fof_unary_formula",
  "fof_infix_unary", "fof_unit_formula", "fof_unitary_formula",
  "fof_quantified_formula", "fof_variable_list", "fof_atomic_formula",
  "fof_plain_atomic_formula", "fof_defined_atomic_formula",
  "fof_defined_plain_formula", "fof_defined_infix_formula",
  "fof_system_atomic_formula", "fof_plain_term", "fof_defined_term",
  "fof_defined_atomic_term", "fof_defined_plain_term", "fof_system_term",
  "fof_arguments", "fof_term", "fof_function_term", "fof_sequent",
  "fof_formula_tuple", "fof_formula_tuple_list",
  "comma_fof_logic_formula_list", "comma_fof_logic_formula", "cnf_formula",
  "cnf_disjunction", "cnf_literal", "thf_quantifier",
  "thf_unary_connective", "th0_quantifier", "type_quantifier",
  "subtype_sign", "tff_unary_connective", "tff_quantifier",
  "fof_quantifier", "nonassoc_connective", "assoc_connective",
  "unary_connective", "gentzen_arrow", "assignment", "identical",
  "type_constant", "type_functor", "defined_type", "atom", "untyped_atom",
  "defined_infix_pred", "infix_equality", "infix_inequality", "constant",
  "functor", "defined_constant", "defined_functor", "system_constant",
  "system_functor", "def_or_sys_constant", "th1_defined_term",
  "distinct_object", "defined_term", "upper_word", "variable", "source",
  "sources", "dag_source", "inference_record", "inference_rule",
  "internal_source", "intro_type", "external_source", "file_source",
  "file_info", "theory", "theory_name", "creator_source", "creator_name",
  "parents", "parent_list", "comma_parent_info_list", "comma_parent_info",
  "parent_info", "parent_details", "optional_info", "useful_info",
  "include", "include_optionals", "formula_selection", "name_list",
  "space_name", "general_term", "general_data", "general_function",
  "formula_data", "general_list", "general_terms",
  "comma_general_term_list", "comma_general_term", "name", "lower_word",
  "single_quoted", "back_quoted", "atomic_word", "dollar_word",
  "dollar_dollar_word", "atomic_defined_word", "atomic_system_word",
  "integer", "rational", "real", "number", "file_name", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-506)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-367)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
    -506,   105,  -506,   791,  -506,   580,   580,   163,   580,   580,
     580,   580,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,
    -506,  -506,  -506,  -506,  -506,  -506,    94,  -506,  -506,  -506,
    -506,  -506,    97,  -506,   124,   136,   149,   168,   178,    78,
      78,    31,   115,    78,    78,    78,    78,   218,   232,   236,
     580,  -506,   245,  -506,   262,   265,   271,   288,  1306,  1412,
     873,   277,   296,   580,  1521,  1432,  2815,   873,  -506,  -506,
    -506,  -506,  -506,  -506,  1306,  1276,  -506,  -506,  -506,  -506,
    -506,  -506,  -506,   196,  -506,  -506,   264,   325,   357,  -506,
     322,   280,  -506,  -506,   335,  -506,   341,  -506,   361,  -506,
    -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,
    -506,  -506,  1306,   873,  1637,  1432,  2815,  1412,  -506,  -506,
    -506,  -506,   374,  -506,  -506,  -506,   388,  -506,  -506,   873,
    -506,  2087,  -506,  -506,   322,  -506,  -506,  -506,  -506,   373,
     434,   142,  -506,  1168,   309,  -506,  -506,  -506,   430,   428,
    2087,  -506,   580,  -506,  -506,   435,  1795,  -506,   322,  -506,
    -506,  -506,   457,   494,   502,  1025,  1432,  -506,  2062,  -506,
    -506,   107,  -506,   507,  -506,   322,  -506,  -506,  -506,  -506,
     466,   518,  1514,   449,  -506,  -506,   688,  -506,  -506,   205,
    -506,  -506,  -506,   727,  -506,  -506,  -506,   357,   430,  -506,
    -506,  -506,  -506,   498,  -506,  2062,   496,  -506,  -506,   100,
     155,   525,  -506,   526,   213,   529,  -506,   387,  -506,  -506,
    1176,  1741,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,
    2991,  -506,  -506,   107,   322,  -506,  -506,  -506,  -506,   480,
     533,   517,  1916,  1441,  -506,  1613,   355,  -506,  -506,   214,
    -506,  -506,  -506,   468,  -506,  -506,   357,   430,  -506,  -506,
     227,  -506,  -506,   493,   479,  -506,  -506,  -506,  -506,  -506,
     520,  1613,  -506,  -506,  -506,  -506,   327,   527,   155,   553,
    -506,   561,   213,   562,  -506,  -506,   419,   322,  -506,   569,
    1637,  -506,   548,  -506,  1637,  -506,  1637,  1337,   574,  1102,
    1637,  1637,  1637,   570,   576,  -506,  -506,  -506,   581,   582,
     584,  -506,   563,  1412,  1412,   597,   598,  2087,  -506,   571,
     605,  2087,  2087,  2087,  -506,  -506,  -506,  -506,   564,  -506,
    2087,  2087,  -506,   318,   627,  -506,  -506,  -506,  -506,   627,
     611,   618,  2033,   512,   512,   612,  -506,  -506,  -506,  -506,
    -506,   621,  2062,  -506,  -506,   164,   592,  -506,  -506,   474,
      85,  -506,  -506,  -506,  -506,   577,   622,  2062,  2062,  2062,
    2062,  2062,  -506,  2062,  1867,  1867,   360,   629,  -506,  -506,
    -506,  -506,   490,  -506,  -506,   627,  -506,    95,  2062,  2062,
    2062,  1054,  1054,   632,  -506,   636,  -506,   564,  -506,   625,
     646,   647,  1613,  -506,  -506,   527,  -506,  2899,  -506,   623,
    -506,  -506,   121,   653,  1613,  1613,  1613,  1613,  1613,  1613,
    1613,  -506,  -506,  -506,   491,  -506,  -506,  2991,  2626,  2626,
     369,  1959,  1959,  1959,  1959,  1959,   627,  -506,  -506,  -506,
    -506,  -506,  2991,    95,  1613,  2991,  2991,  2991,   660,  -506,
     652,  -506,  -506,  1337,   163,   163,   163,   163,   163,  -506,
     645,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,
    -506,   655,   663,   669,   672,  -506,  -506,  -506,  -506,  -506,
     670,  -506,  -506,   675,  -506,  -506,   679,  -506,  -506,  -506,
    -506,  -506,  -506,  -506,  -506,  -506,   635,   689,   650,   694,
    -506,   691,  -506,  -506,  2033,  2033,  -506,  -506,  -506,   656,
     657,  -506,  -506,   674,  -506,   702,  -506,  -506,  -506,  -506,
     682,   708,   508,   503,   710,  -506,   926,  -506,  -506,  -506,
    -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  2062,
    -506,  -506,  -506,  -506,  -506,  2062,   686,  -506,  -506,  -506,
     715,   721,   745,   718,   744,  3068,   505,  -506,  -506,   746,
    -506,  2272,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,
    -506,  -506,  2899,  -506,  -506,  -506,  -506,  -506,  2899,  -506,
    -506,   703,  -506,  -506,  -506,  -506,  -506,  -506,   729,   755,
     756,   517,   747,   753,  -506,   703,  -506,  -506,  -506,  -506,
     765,  -506,   777,   781,  -506,  -506,   780,   758,   784,  -506,
     786,   789,  -506,   790,  -506,   645,  -506,   378,  -506,  -506,
    1637,  -506,  -506,  1412,  -506,  -506,  2087,  -506,   787,   627,
     794,   627,   651,   802,   416,   803,    67,   810,   792,   651,
     627,   651,  -506,   512,  2062,  -506,   811,  -506,   815,  -506,
    2062,  -506,  1867,   816,  -506,   831,   832,  -506,  -506,   837,
     838,   833,  -506,  -506,  -506,  -506,  1054,  2991,   815,   836,
    -506,  2991,  -506,  2276,   816,  -506,   844,   864,  -506,  -506,
     868,   869,   865,   627,  2991,  -506,  -506,  -506,  1337,  -506,
     378,   580,   874,   378,   378,   875,  -506,  -506,  -506,  -506,
    -506,  2087,  -506,  1667,  -506,   651,  -506,  -506,   651,  -506,
    -506,   651,  2033,  -506,  -506,   848,   876,   877,  -506,   878,
     879,   853,   431,  2062,  -506,  2062,  -506,  -506,  -506,   926,
    -506,  -506,  2062,  -506,   815,   880,   860,  2991,  2991,  -506,
    -506,  -506,  -506,  2272,  -506,  -506,  -506,  -506,  -506,  -506,
     887,  -506,  -506,   888,   889,  -506,  -506,  -506,   803,  -506,
    -506,  -506,   886,   651,  -506,   773,  -506,   896,  -506,  -506,
    -506,  2991,  -506,  -506,   897,  -506,   473,   473,   473,  2119,
    -506,  -506,  -506,  -506,  -506,  1337,  -506,   901,   902,   905,
     742,  -506,  -506,  -506,   904,   884,  -506,  -506,  -506,  -506,
     742,   908,  1412,  -506,  -506,   910,   863,  -506,  -506,  1337,
    -506,  -506
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int16 yydefact[] =
{
       4,     0,     2,     3,     1,     0,     0,     0,     0,     0,
       0,     0,     5,     6,    13,     8,     9,    10,    11,    12,
       7,   457,   458,   456,   466,   455,     0,   459,   460,   461,
     453,   454,     0,   472,   424,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    23,     0,
       0,   428,   425,   423,     0,     0,     0,     0,     0,     0,
       0,     0,   429,     0,     0,     0,     0,     0,   383,   462,
     463,   386,   468,   467,     0,     0,   330,   327,   290,   291,
     294,   295,   292,   293,   313,   302,   296,   298,     0,   310,
      22,   323,   325,   299,   370,   304,   372,   306,   374,   385,
     301,   387,   311,   371,   464,   465,   373,   375,   469,   470,
     471,   384,     0,     0,     0,     0,     0,     0,   447,   439,
     437,    24,   432,   436,   440,   434,   435,   438,   346,     0,
     347,     0,   317,   356,    22,   265,   267,   270,   271,   273,
     274,   283,   280,     0,   282,   284,   285,   266,     0,     0,
       0,   427,     0,   426,   431,     0,     0,   261,    22,   260,
     262,   263,     0,   299,   306,     0,     0,   259,     0,   256,
     204,     0,   258,     0,   345,    22,   130,   135,   139,   140,
     142,   143,     0,   148,   157,   155,   149,   166,   167,   156,
     170,   171,   175,   150,   172,   179,   178,     0,   201,   131,
     132,   137,   138,     0,   343,     0,     0,   344,   342,     0,
     173,   370,   176,   372,   181,   374,   200,   159,   378,   339,
       0,     0,   368,   340,   379,   337,   338,   382,   380,   381,
       0,   101,   336,     0,    22,    25,    30,    34,    35,    38,
      39,    40,     0,    48,    55,     0,    49,    64,    65,    56,
      68,    69,    75,    50,    70,    78,     0,    73,    71,    26,
       0,    36,   118,   119,   120,    27,    32,    33,    77,   335,
       0,     0,   332,   333,   331,   334,     0,     0,    72,   370,
      74,   372,    82,   374,    80,    79,    57,    22,    15,     0,
       0,   328,     0,   369,     0,   367,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   312,   303,   314,     0,     0,
       0,   450,     0,     0,     0,     0,     0,     0,   320,     0,
       0,     0,     0,     0,   350,   348,   351,   349,     0,   353,
       0,     0,   357,     0,     0,   283,   279,   282,   430,     0,
       0,     0,     0,     0,     0,     0,   184,   365,   370,   366,
     374,     0,     0,   196,   207,   198,     0,   173,   181,   197,
       0,   376,   372,   377,   254,     0,     0,     0,     0,     0,
       0,     0,   359,     0,     0,     0,     0,     0,   168,   153,
     154,   152,   156,   151,   201,     0,   341,     0,     0,     0,
       0,     0,     0,     0,    84,     0,   355,   356,   354,     0,
       0,     0,   100,    96,    97,    98,    99,     0,   108,     0,
      72,    82,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    59,    48,    49,    56,    50,    73,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    66,    53,    54,
      52,    51,     0,     0,     0,     0,     0,     0,     0,   324,
       0,   297,   281,     0,     0,     0,     0,     0,     0,   388,
     421,   389,   396,   390,   391,   401,   402,   403,   395,    20,
     326,     0,   308,     0,     0,   445,   444,   446,   443,   442,
     449,   448,   433,     0,   286,   316,   319,   318,    19,   276,
     278,   277,   352,   275,   272,   315,     0,   288,     0,   161,
     163,   164,   211,    18,     0,     0,   210,   213,   215,     0,
     212,   214,   228,     0,   223,   360,   224,   225,   361,   362,
       0,   186,     0,   158,   206,   205,     0,   247,   257,    17,
     145,   148,   149,   150,   147,   146,   144,   141,   238,     0,
     199,   180,   202,   169,   239,     0,     0,   237,   363,   364,
       0,     0,     0,     0,    86,     0,    58,    76,   112,   107,
     102,     0,   240,    16,    42,    44,    47,    43,    46,    41,
      37,   128,     0,    93,    81,    94,    67,   129,     0,   116,
      56,   121,   122,    57,   123,   125,   124,   126,     0,    61,
       0,   117,     0,   116,   111,   113,   115,   114,   127,    45,
       0,   106,     0,     0,    14,   329,   393,     0,     0,   410,
     406,     0,   398,     0,   400,   421,   408,     0,    21,   300,
       0,   305,   307,     0,   451,   441,     0,   321,     0,     0,
       0,     0,     0,     0,     0,   221,     0,   235,     0,     0,
       0,     0,   185,     0,     0,   191,     0,   188,     0,   192,
       0,   208,     0,     0,   253,     0,   249,   252,   251,     0,
       0,     0,   174,   177,   182,    85,     0,     0,     0,     0,
      88,     0,   109,     0,     0,   246,     0,   242,   245,   244,
       0,     0,     0,     0,     0,   103,   104,   105,     0,   392,
       0,     0,     0,     0,     0,     0,   420,   422,   309,   452,
     322,     0,   289,     0,   162,     0,   165,   216,     0,   227,
     222,     0,     0,   234,   231,     0,   229,     0,   187,   170,
     193,     0,   198,     0,   358,     0,   209,   255,   248,     0,
     203,   195,     0,    87,   108,    91,     0,     0,     0,   110,
     100,    98,   241,     0,    95,    58,    60,    62,    63,   394,
       0,   405,   404,     0,     0,   407,   287,   264,     0,   232,
     233,   236,     0,     0,   226,     0,   189,     0,   190,   250,
     160,     0,    89,    90,     0,   243,     0,     0,     0,     0,
     230,   194,   183,    92,    83,     0,   411,     0,     0,     0,
       0,   220,   217,   218,   419,     0,   414,   409,   397,   399,
       0,     0,     0,   417,   412,   413,     0,   219,   418,     0,
     415,   416
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,
    -506,  -506,  -506,   334,   724,   826,   -27,  -506,  -506,  -506,
    -506,  -506,  -378,  -159,  -506,   654,  -506,  -506,   261,  -506,
     418,  -192,  -177,   534,  -506,  -506,  -506,    25,  -506,  -506,
    -506,   281,  -506,   400,   186,  -116,  -506,    -9,  -506,  -125,
    -193,  -506,  -506,  -158,   286,  -314,  -506,  -506,  -387,  -506,
    -506,  -506,  -505,  -506,   849,   -32,  -506,  -506,  -506,  -506,
    -506,  -231,  -506,  -184,  -506,  -506,  -350,  -506,  -506,  -209,
     766,   768,   113,  -412,  -506,  -506,  -128,  -506,  -506,  -506,
     331,  -506,   459,  -506,   217,  -506,  -295,  -284,    83,  -238,
    -506,  -506,   -49,   659,   488,   219,  -506,  -481,   392,   234,
     209,  -506,  -506,   291,  -506,  -479,  -506,  -506,   263,  -506,
    -506,  -506,   275,  -506,  -506,   774,  -476,   620,  -506,   310,
    -506,    63,   -93,  -506,  -506,  -506,  -506,  -506,  -122,   -15,
    -108,  -104,  -506,   391,   -24,  -506,  -506,  -506,  -506,  -506,
      56,  -506,  -506,   114,   123,  -221,   -14,  -506,   894,   692,
    -506,  -506,  -506,    37,  -506,   728,  -506,  -118,  -506,  -227,
     754,  -506,   648,    -7,   -51,  -506,  2330,   -75,   393,  -208,
    -506,  -506,  -506,   599,   -46,  -101,   -40,   -20,   500,   846,
    1884,  2230,  1192,  1538,  -506,  -506,   -50,  2082,  -506,   -41,
    -275,   347,  -506,  -506,  -506,  -506,  -506,  -506,  -506,  -506,
    -506,  -506,  -506,  -506,  -345,  -506,  -506,  -506,   231,  -506,
     429,  -351,  -506,  -506,  -506,   891,  -506,   -42,  -506,  -506,
    -506,  -488,   732,  -506,  -506,    21,   940,  -506,  -506,    -5,
    -506,  -506,   614,  -506,     2,  -506,  -506,   -45,   593
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
       0,     1,     2,     3,    12,    13,    14,   287,    15,    16,
      17,    18,    19,   298,    47,   234,   408,   236,   237,   238,
     239,   240,   241,   242,   437,   243,   244,   245,   588,   589,
     246,   247,   248,   249,   250,   251,   252,   253,   254,   255,
     393,   553,   669,   735,   736,   256,   400,   426,   258,   600,
     601,   559,   672,   259,   594,   260,   596,   261,   262,   263,
     264,   265,   266,   267,   175,   353,   177,   178,   179,   180,
     181,   182,   378,   183,   184,   185,   498,   499,   500,   186,
     187,   188,   189,   190,   191,   192,   193,   194,   195,   345,
     520,   646,   720,   648,   721,   196,   354,   197,   384,   356,
     524,   651,   340,   637,   507,   508,   792,   509,   510,   717,
     511,   636,   512,   638,   200,   201,   202,   268,   676,   677,
     678,   203,   655,   656,   657,   360,   658,   269,   158,   159,
     160,   134,   135,   136,   137,   138,   139,   140,   141,   142,
     143,   144,   145,   496,   146,    78,    79,    80,    81,    82,
      83,    84,    85,    86,    87,   471,    88,    89,   147,   148,
     319,   486,   627,   161,    91,    92,   270,   271,   272,   273,
     387,   205,   274,   207,   403,   404,   275,   376,   737,   373,
     514,   515,   516,   547,   162,   294,   277,   406,   410,   279,
     280,   281,   411,   283,   364,   284,    99,   285,   101,   102,
     606,   607,   461,   462,   611,   463,   613,   464,   465,   692,
     466,   615,   467,   608,   787,   795,   805,   810,   796,   803,
     618,   696,    20,    42,    52,    61,   153,   311,   122,   123,
     124,   125,   312,   480,   624,   468,    27,    28,    29,   103,
     104,   105,   106,   107,   108,   109,   110,   111,    34
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      30,    30,    33,    30,    30,    30,    30,    31,    31,   119,
      31,    31,    31,    31,   127,   157,   199,   121,   120,   209,
     276,   379,   460,   634,   217,   286,    26,    32,   335,    35,
      36,    37,    38,   176,    77,   546,   315,   409,   318,   235,
      77,   427,   336,    76,   582,    30,   337,   654,   295,    76,
      77,   291,    31,   149,   126,   597,   675,   257,    30,    76,
     149,   292,   394,   401,   591,    31,   199,   119,   296,   209,
     276,    62,   127,   333,   217,   286,   120,   383,   538,   439,
     473,   474,    50,   176,   154,   679,   421,    23,    77,   235,
     541,   543,   331,   710,   440,    90,   374,    76,    21,    22,
     308,    69,    70,   402,    23,     4,   149,   257,    51,   526,
     645,   289,   126,    69,    70,   513,   346,   581,   584,   585,
     586,   587,   149,    39,   149,   217,    40,   217,   595,   697,
     288,   371,    77,   342,   351,   386,   530,   534,   535,   536,
     537,    76,    53,   149,   711,   561,    25,    30,   198,   303,
     550,   551,   552,    41,    31,   428,   527,   295,   532,   532,
     532,   532,   532,    25,   217,    43,    21,    22,  -268,  -268,
     305,  -268,    23,    62,   395,   395,   304,   375,    44,  -201,
     286,   405,   430,   531,   531,   531,   531,   531,  -365,   286,
    -365,   420,   562,   289,   399,   332,  -268,    45,   198,   335,
     335,   335,   697,  -201,   286,   697,   697,    46,   335,   335,
     439,  -312,   257,   489,   490,   491,   295,   337,   337,   337,
    -199,   257,   493,   494,   315,   440,   337,   337,   306,   -93,
     286,    25,   719,   401,   554,  -312,   429,   307,   675,   533,
     533,   533,   533,   533,  -199,   372,  -366,    58,  -366,   198,
     654,   355,   295,   -93,   372,   564,   565,   566,   567,   568,
     569,   570,    59,   119,   119,    60,   450,   679,   127,   127,
     425,   482,   120,   120,    63,    77,   292,   513,   513,  -303,
     451,   704,   452,   592,    76,   599,   472,   472,   472,   402,
     715,    64,    30,   497,    65,   521,   441,   597,   501,    31,
      66,   517,   431,  -303,   432,   433,   591,   660,   126,   126,
     149,   217,   574,   576,   149,   149,   149,    67,   382,   806,
     351,   602,   603,   149,   149,   152,   217,   217,   217,   217,
     217,   151,   217,   542,   542,  -269,  -269,   518,  -269,   750,
    -314,   548,   753,   754,   501,   395,   395,   217,   217,   217,
     305,   297,   305,   645,   299,   726,   305,   305,   305,   300,
     442,   286,   386,  -269,  -314,   301,   286,   405,   727,   131,
     595,   132,   293,   286,   286,   286,   286,   286,   286,   286,
     399,   -29,   -29,   -29,   -29,   302,   286,   575,   575,   -29,
     583,   583,   583,   583,   583,   590,   222,   548,   257,   698,
     571,   286,  -202,   286,   286,   286,   286,   313,   306,   -29,
     306,   168,   314,   170,   306,   306,   306,   307,   257,   307,
     230,   577,   231,   307,   307,   307,  -202,   441,   767,   117,
     768,   118,   788,   789,   -94,   198,   257,   257,   257,   425,
     425,   425,   425,   425,   425,   425,  -201,   321,    30,   609,
      33,   612,   614,   616,   402,    31,   355,   322,   -94,   544,
     402,   332,   332,   517,   517,  -192,   427,   425,   320,   425,
    -201,   355,   355,   355,   409,  -133,  -133,  -133,  -133,   334,
     382,   382,   382,   382,   382,   513,   339,   540,   540,  -200,
     342,   639,   341,   708,   -31,   -31,   -31,   -31,   217,   518,
     518,   770,   -31,  -133,   217,  -199,   -93,   659,   554,   366,
     794,    21,    22,  -200,   286,    21,    22,    23,  -203,    70,
     -95,    23,   -31,   532,   785,   592,   786,  -365,   668,  -199,
     -93,   286,   405,   700,   794,  -366,   343,   286,   405,   365,
     367,   368,  -203,   377,   -95,   680,   257,   385,   531,   388,
     389,   681,   513,   390,   414,   740,   415,   435,    93,   644,
      93,   170,   416,   257,   163,   210,   278,    93,   413,   257,
     434,   436,   444,   119,    93,    93,    25,   445,   127,   335,
      25,   699,   120,    21,    22,   446,   447,   222,   497,    23,
     501,   517,    24,   756,   521,   449,   475,   337,   517,   501,
     517,   469,   476,   217,   533,   649,   472,   477,   478,   217,
     479,   542,    93,    93,    93,   210,   278,   481,   126,   149,
     395,   448,   198,   484,   485,   487,   286,   518,   355,    93,
     286,    93,   488,   741,   518,    71,   518,   502,   492,   653,
     734,   522,   590,   286,   739,   503,   525,   523,    25,   529,
      93,   556,   528,   545,    21,    22,   163,    69,   257,    71,
      23,   555,   257,   423,   517,   347,   210,   517,   357,   442,
     517,   517,   557,   558,   617,   705,   305,   560,   605,    77,
     563,   619,   217,    30,   217,   204,    30,   604,    76,   628,
      31,   217,   620,    31,   149,   621,   286,   286,   622,   623,
     518,   625,   505,   518,   630,   357,   518,   518,   626,   425,
     773,   774,   751,   206,  -134,  -134,  -134,  -134,   629,    25,
     347,   278,   517,   631,   632,   640,   641,   722,   257,   257,
     286,   639,  -221,   355,   306,   204,   642,   643,   517,   650,
     661,   662,  -134,   307,   668,    21,    22,   663,    69,   517,
      71,    23,   119,  -136,  -136,  -136,  -136,   127,   518,   517,
     808,   120,   257,   206,    49,   540,   800,    54,    55,    56,
      57,   664,   665,   666,   518,   671,    21,    22,   431,   424,
      30,  -136,    23,   682,   683,   518,   204,    31,   204,   684,
      93,   685,   418,   505,    93,   518,    93,   126,   -48,    93,
      93,    93,    93,   686,    30,   424,   355,   687,   355,   688,
      25,    31,   689,   690,   206,   691,   206,    93,   693,   694,
     701,    93,    93,    93,   168,   204,   170,   703,   707,   709,
      93,    93,   423,   423,   423,   423,   423,   423,   423,   712,
     723,    25,   653,   347,   347,   382,   713,     5,   649,   724,
       6,     7,   357,   206,     8,     9,   372,    10,    11,   728,
     423,   729,   423,   730,   731,   738,   732,   357,   357,   357,
     357,   357,   742,   357,   357,   357,    21,    22,    68,    69,
      70,    71,    23,    72,    73,    24,   128,   347,   357,   357,
     357,   347,   347,   743,   744,   745,   635,   129,   746,   422,
     752,   755,   762,   764,    94,   763,    94,   766,   765,   771,
      94,   211,  -191,    94,   772,   130,   776,   777,   778,   779,
      94,    94,   782,   784,   131,   438,   132,   797,   798,    21,
      22,   799,    69,    70,   807,    23,   424,   802,   804,   809,
     708,    25,   310,   347,   747,   133,   165,   733,   424,   424,
     424,   424,   424,   424,   424,   670,   519,   783,    94,    94,
      94,   211,   573,   573,   309,   580,   580,   580,   580,   580,
     748,   380,   204,   381,   718,    94,   424,    94,   424,    48,
      48,   647,   781,    48,    48,    48,    48,   204,   204,   204,
     204,   204,   633,   204,    25,   171,    94,   780,   791,   801,
     206,   506,    94,   761,   769,   652,   775,   412,   204,   204,
     204,   348,   211,   757,   211,   206,   206,   206,   206,   206,
     702,   206,   357,   316,   706,   495,   357,   470,    21,    22,
     443,   714,    70,   716,    23,   749,   206,   206,   206,   357,
     811,   725,   598,   338,   695,   357,   483,     0,   610,   343,
       0,   211,     0,     0,     0,     0,   438,    21,    22,     0,
       0,    70,     0,    23,     0,     0,   348,     0,   422,   422,
     422,   422,   422,   422,   422,     0,   344,     0,   391,     0,
       0,     0,     0,     0,     0,   579,   579,   579,   579,   579,
       0,     0,     0,    25,     0,   674,   593,   758,   422,     0,
     759,     0,   423,   760,     0,    21,    22,    68,    69,    70,
      71,    23,    72,    73,    24,     0,     0,     0,   519,   519,
      93,     0,    25,     0,     0,     0,    93,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    94,     0,     0,     0,
      94,     0,    94,   347,   357,    94,    94,    94,    94,     0,
     357,     0,   357,     0,     0,   716,     0,     0,     0,   204,
       0,     0,     0,    94,     0,   204,   347,    94,    94,    94,
      25,   793,     0,     0,    75,     0,    94,    94,     0,    21,
      22,     0,   635,    70,     0,    23,     0,   206,     0,   348,
     348,   323,   635,   206,     0,     0,     0,     0,   211,     0,
     391,    93,     0,    93,   324,   325,   326,     0,     0,   327,
       0,     0,     0,   211,   211,   211,   211,   211,   424,   211,
     211,   211,     0,   357,     0,   357,     0,   392,     0,   357,
       0,     0,   357,   348,   211,   211,   211,   348,   348,     0,
     328,   329,   330,     0,    25,     0,   519,     0,     0,     0,
      97,     0,    97,   519,     0,   519,   164,   214,   282,    97,
       0,     0,     0,     0,   204,   357,    97,    97,     0,     0,
     204,     0,     0,     0,     0,     0,     0,   674,     0,    21,
      22,    68,    69,    70,    71,    23,    72,    73,    24,   348,
       0,     0,   206,     0,     0,     0,     0,     0,   206,     0,
     290,     0,     0,     0,    97,    97,    97,   214,   282,    21,
      22,    68,    69,    70,    71,    23,    72,    73,    24,   519,
       0,    97,   519,    97,     0,   519,   519,     0,     0,     0,
      74,     0,     0,     0,     0,     0,     0,     0,   593,     0,
      21,    22,    97,   204,    25,   204,    23,     0,   164,    24,
       0,     0,   204,     0,     0,     0,     0,   349,   214,     0,
     358,     0,     0,   363,     0,     0,     0,     0,   211,     0,
       0,   206,   211,   206,    25,     0,     0,   519,    75,     0,
     206,     0,     0,     0,     0,   211,     0,     0,   453,     0,
       0,   211,     0,   519,   454,   455,     0,   358,   456,   457,
       0,     0,   458,     0,   519,   459,     0,     0,     0,     0,
       0,     0,   349,   282,   519,    21,    22,    68,     0,     0,
      71,    23,    72,    73,    24,   363,     0,     0,     0,   112,
     113,   114,     0,   115,   116,    21,    22,    68,    69,    70,
      71,    23,    72,    73,    24,   128,     0,     0,     0,     0,
       0,     0,   165,     0,     0,     0,   166,   167,     0,     0,
       0,     0,     0,   117,     0,   118,    94,   -28,   -28,   -28,
     -28,     0,    94,     0,   130,   -28,     0,     0,     0,     0,
      25,     0,    97,   168,   169,   170,    97,     0,    97,   348,
     211,    97,    97,    97,    97,   -28,   211,     0,   211,     0,
      25,   171,   172,     0,   133,     0,     0,     0,   173,    97,
       0,   174,   348,    97,    97,    97,  -116,     0,  -116,  -116,
       0,     0,    97,    97,    21,    22,    68,    69,    70,    71,
      23,    72,    73,    24,   155,   349,   349,   369,     0,     0,
       0,     0,     0,     0,   358,   156,     0,    94,     0,    94,
     324,   325,   326,     0,     0,   327,     0,     0,     0,   358,
     358,   358,   358,   358,     0,   358,   358,   358,     0,   211,
       0,   211,     0,     0,     0,   211,     0,     0,   211,   349,
     358,   358,   358,   349,   349,     0,   328,   329,   370,    25,
       0,     0,     0,    75,     0,     0,    98,     0,    98,     0,
       0,     0,    98,   215,     0,    98,     0,     0,     0,     0,
       0,   211,    98,    98,     0,     0,    21,    22,    68,    69,
      70,    71,    23,    72,    73,    24,   128,   218,     0,   219,
       0,     0,     0,   220,     0,   349,     0,   407,   167,     0,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
      98,    98,    98,   215,     0,   130,   223,   224,     0,   225,
     226,   227,   228,   229,   230,   169,   231,    98,   232,    98,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
     155,    25,   233,   172,     0,   133,     0,     0,    98,   173,
       0,    74,   174,     0,    98,     0,     0,     0,     0,     0,
       0,     0,     0,   350,   215,    25,   215,     0,     0,   350,
       0,     0,     0,     0,     0,     0,     0,     0,   358,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   358,     0,     0,     0,    25,     0,   358,     0,    75,
       0,     0,     0,   215,    21,    22,    68,    69,    70,    71,
      23,    72,    73,    24,   128,   218,   293,   219,   350,     0,
       0,   220,     0,     0,   396,   221,   167,     0,     0,     0,
       0,   350,     0,     0,     0,     0,     0,   324,   325,   326,
     222,     0,   327,   130,   223,   224,     0,   225,   226,   227,
     228,   229,   230,   169,   231,     0,   232,     0,    21,    22,
      68,    69,    70,    71,    23,    72,    73,    24,     0,    25,
     233,   172,    97,   397,   329,   398,     0,   173,    97,   156,
     174,     0,     0,     0,     0,     0,     0,     0,    98,     0,
       0,     0,    98,     0,    98,   349,   358,    98,    98,    98,
      98,     0,   358,     0,   358,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    98,     0,     0,   349,    98,
      98,    98,     0,    25,     0,     0,     0,    75,    98,    98,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
       0,   350,   350,     0,     0,     0,     0,   165,     0,     0,
     215,   539,     0,    97,     0,    97,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   215,   215,   215,   215,   215,
       0,   215,   215,   215,     0,   358,     0,   358,   168,     0,
     170,   358,     0,     0,   358,   350,   215,   215,   215,   350,
     350,     0,     0,     0,     0,    25,   171,     0,     0,   417,
       0,     0,    95,     0,    95,     0,     0,     0,    95,   212,
       0,    95,   324,   325,   326,     0,     0,   327,    95,    95,
       0,   418,    21,    22,    68,    69,    70,    71,    23,    72,
      73,    24,   128,   218,     0,   219,     0,     0,     0,   220,
       0,   350,     0,   578,     0,     0,     0,     0,   328,   329,
     419,     0,     0,     0,     0,     0,    95,    95,    95,   212,
       0,   130,   223,   224,     0,   225,   226,   227,   228,   229,
     230,     0,   231,    95,   232,    95,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    25,   233,     0,
       0,     0,     0,     0,    95,     0,    21,    22,   174,    69,
      95,    71,    23,     0,     0,     0,     0,     0,     0,   219,
     212,     0,   212,     0,     0,   361,     0,   504,     0,     0,
       0,     0,     0,     0,   215,    21,    22,    68,    69,    70,
      71,    23,    72,    73,    24,   128,   223,   215,     0,     0,
       0,     0,   165,   215,   505,     0,   352,   167,     0,   212,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
     128,    25,     0,     0,   130,     0,     0,     0,     0,     0,
       0,   317,     0,   168,   169,   170,     0,   361,     0,     0,
       0,     0,    21,    22,     0,    69,     0,    71,    23,   130,
      25,   171,   172,     0,   133,   219,     0,     0,   173,     0,
     100,   174,   100,   790,     0,     0,   100,   216,     0,   100,
       0,     0,     0,     0,     0,    25,   100,   100,    98,   133,
       0,     0,   223,     0,    98,     0,     0,     0,     0,     0,
     505,     0,     0,     0,    95,     0,     0,     0,    95,     0,
      95,   350,   215,    95,    95,    95,    95,    25,   215,     0,
     215,     0,     0,     0,   100,   100,   100,   216,     0,     0,
       0,    95,     0,     0,   350,    95,    95,    95,     0,     0,
       0,   100,     0,   100,    95,    95,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   100,     0,     0,     0,   212,     0,   100,    98,
       0,    98,     0,     0,     0,     0,     0,     0,   216,     0,
     359,   212,   212,   212,   212,   212,     0,   212,   212,   212,
       0,   215,     0,   215,     0,     0,     0,   215,     0,     0,
     215,   549,   212,   212,   212,    21,    22,    68,    69,    70,
       0,    23,    72,    73,    24,     0,   218,   216,    96,     0,
      96,   293,   220,     0,    96,   213,   673,    96,     0,   396,
       0,   167,     0,     0,    96,    96,     0,     0,     0,     0,
       0,     0,   324,   325,   326,   222,   224,   327,     0,     0,
     227,   228,   229,   230,     0,   231,     0,   549,   169,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      25,   233,    96,    96,    96,   213,   172,     0,   397,   329,
     398,   652,   173,     0,     0,     0,     0,     0,     0,    96,
       0,    96,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   100,     0,     0,     0,   100,     0,   100,     0,
      96,   100,   100,   100,   100,     0,    96,     0,     0,     0,
     150,     0,     0,     0,     0,   208,   213,   150,   213,   100,
       0,   362,     0,   100,   100,   100,     0,     0,     0,     0,
     212,     0,   100,   100,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   212,     0,     0,     0,     0,     0,   212,
       0,     0,     0,     0,   216,   213,     0,     0,     0,     0,
       0,     0,     0,   150,     0,   208,     0,     0,     0,   216,
     216,   216,   216,   216,     0,   359,   216,   216,     0,   150,
       0,   150,     0,   362,     0,     0,     0,     0,     0,     0,
     359,   359,   359,     0,     0,     0,     0,     0,     0,     0,
     150,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   208,     0,   208,     0,
       0,     0,     0,     0,    95,     0,     0,     0,     0,     0,
      95,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      96,     0,     0,     0,    96,     0,    96,     0,   212,    96,
      96,    96,    96,     0,   212,   208,   212,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    96,     0,     0,
       0,    96,    96,    96,     0,     0,     0,     0,     0,     0,
      96,    96,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   213,     0,     0,    95,     0,    95,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   213,   213,   213,
     213,   213,     0,   213,   213,   213,     0,   212,     0,   212,
       0,     0,     0,   212,     0,     0,   212,   362,   213,   213,
     213,   216,     0,     0,     0,     0,     0,   359,     0,    21,
      22,    68,    69,    70,    71,    23,    72,    73,    24,     0,
     218,     0,     0,     0,     0,     0,   220,   150,     0,     0,
     572,   150,   150,   150,     0,     0,     0,     0,     0,     0,
     150,   150,     0,     0,     0,     0,     0,     0,     0,     0,
     224,     0,     0,   362,   227,   228,   229,   230,     0,   231,
       0,     0,   208,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    25,   233,     0,   208,   208,   208,
     208,   208,   100,   208,     0,     0,     0,     0,   100,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   208,   208,
     208,     0,     0,     0,     0,     0,   359,     0,     0,     0,
       0,     0,   359,     0,   216,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   213,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   213,
       0,     0,     0,     0,     0,   213,     0,     0,     0,     0,
       0,     0,     0,   100,     0,   100,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   359,     0,   359,     0,     0,
       0,     0,     0,     0,   216,     0,     0,     0,    21,    22,
      68,    69,    70,    71,    23,    72,    73,    24,   128,   218,
       0,   219,     0,     0,     0,   220,     0,     0,     0,   221,
     167,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      96,     0,     0,     0,   222,     0,    96,   130,   223,   224,
       0,   225,   226,   227,   228,   229,   230,   169,   231,   208,
     232,     0,     0,     0,   213,   208,     0,     0,     0,     0,
     213,     0,   213,    25,   233,   172,     0,   133,     0,     0,
       0,   173,     0,     0,   174,     0,     0,     0,     0,     0,
       0,     0,    21,    22,    68,    69,    70,    71,    23,    72,
      73,    24,   128,   218,   293,   219,     0,     0,     0,   220,
       0,     0,   396,   407,   167,     0,     0,     0,     0,     0,
       0,    96,     0,    96,     0,   324,   325,   326,   222,     0,
     327,   130,   223,   224,     0,   225,   226,   227,   228,   229,
     230,   169,   231,   213,   232,   213,   150,     0,     0,   213,
       0,     0,   213,     0,     0,     0,     0,    25,   233,   172,
       0,   397,   329,   398,   208,   173,     0,     0,   174,     0,
     208,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    21,    22,    68,    69,    70,    71,
      23,    72,    73,    24,   128,   218,     0,   219,     0,     0,
       0,   220,     0,     0,     0,   407,   167,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     222,   150,     0,   130,   223,   224,     0,   225,   226,   227,
     228,   229,   230,   169,   231,     0,   232,     0,     0,     0,
       0,     0,     0,   208,     0,   208,     0,     0,     0,    25,
     233,   172,   208,   133,     0,     0,     0,   173,     0,     0,
     174,    21,    22,    68,    69,    70,    71,    23,    72,    73,
      24,   128,   218,     0,   219,     0,     0,     0,   220,     0,
       0,     0,   407,   167,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   222,     0,     0,
     130,   223,   224,     0,   225,   226,   227,   228,   229,   667,
     169,   231,     0,   232,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    25,   233,   172,     0,
     133,     0,     0,     0,   173,     0,     0,   174
};

static const yytype_int16 yycheck[] =
{
       5,     6,     7,     8,     9,    10,    11,     5,     6,    59,
       8,     9,    10,    11,    59,    64,    65,    59,    59,    65,
      66,   205,   297,   504,    65,    66,     5,     6,   150,     8,
       9,    10,    11,    65,    58,   385,   129,   230,   131,    66,
      64,   249,   150,    58,   431,    50,   150,   526,    88,    64,
      74,    75,    50,    60,    59,   442,   561,    66,    63,    74,
      67,    75,   220,   221,   442,    63,   115,   117,    88,   115,
     116,    50,   117,   148,   115,   116,   117,   205,   373,   271,
     301,   302,    51,   115,    63,   561,   245,     9,   112,   116,
     374,   375,   143,    26,   271,    58,   197,   112,     3,     4,
     114,     6,     7,   221,     9,     0,   113,   116,    77,    24,
     522,    74,   117,     6,     7,   342,   165,   431,   432,   433,
     434,   435,   129,    29,   131,   166,    29,   168,   442,   617,
      67,   182,   156,    33,   166,    35,   367,   368,   369,   370,
     371,   156,    27,   150,    77,    24,    68,   152,    65,   112,
     388,   389,   390,    29,   152,   256,    71,   197,   367,   368,
     369,   370,   371,    68,   205,    29,     3,     4,    26,    27,
     114,    29,     9,   152,   220,   221,   113,   197,    29,    15,
     221,   221,   257,   367,   368,   369,   370,   371,    33,   230,
      35,   242,    71,   156,   221,    31,    54,    29,   115,   321,
     322,   323,   690,    39,   245,   693,   694,    29,   330,   331,
     402,    15,   221,   321,   322,   323,   256,   321,   322,   323,
      15,   230,   330,   331,   317,   402,   330,   331,   114,    15,
     271,    68,   644,   391,   392,    39,   256,   114,   743,   367,
     368,   369,   370,   371,    39,    40,    33,    29,    35,   166,
     729,   168,   292,    39,    40,   414,   415,   416,   417,   418,
     419,   420,    30,   313,   314,    29,   290,   743,   313,   314,
     245,   313,   313,   314,    29,   299,   290,   504,   505,    15,
     294,   631,   296,   442,   299,   444,   300,   301,   302,   407,
     640,    29,   297,   334,    29,   344,   271,   684,   339,   297,
      29,   342,    75,    39,    77,    78,   684,   545,   313,   314,
     317,   352,   428,   429,   321,   322,   323,    29,   205,   800,
     352,   446,   447,   330,   331,    29,   367,   368,   369,   370,
     371,    54,   373,   374,   375,    26,    27,   342,    29,   690,
      15,   387,   693,   694,   385,   391,   392,   388,   389,   390,
     294,    29,   296,   765,    74,   650,   300,   301,   302,    24,
      33,   402,    35,    54,    39,    24,   407,   407,   652,    51,
     684,    53,    15,   414,   415,   416,   417,   418,   419,   420,
     407,    26,    27,    28,    29,    24,   427,   428,   429,    34,
     431,   432,   433,   434,   435,   436,    39,   443,   407,   620,
     427,   442,    15,   444,   445,   446,   447,    33,   294,    54,
     296,    51,    24,    53,   300,   301,   302,   294,   427,   296,
      51,   430,    53,   300,   301,   302,    39,   402,   723,    51,
     725,    53,   777,   778,    15,   352,   445,   446,   447,   414,
     415,   416,   417,   418,   419,   420,    15,    74,   453,   454,
     455,   456,   457,   458,   572,   453,   373,    23,    39,   376,
     578,    31,    31,   504,   505,    34,   674,   442,   134,   444,
      39,   388,   389,   390,   667,    26,    27,    28,    29,    51,
     367,   368,   369,   370,   371,   712,    51,   374,   375,    15,
      33,    75,   158,    77,    26,    27,    28,    29,   539,   504,
     505,   732,    34,    54,   545,    15,    15,   539,   666,   175,
     785,     3,     4,    39,   555,     3,     4,     9,    15,     7,
      15,     9,    54,   732,    51,   684,    53,    33,   555,    39,
      39,   572,   572,   626,   809,    33,    24,   578,   578,    32,
      74,    23,    39,    45,    39,   572,   555,    51,   732,    24,
      24,   578,   779,    24,    74,   673,    23,    78,    58,    51,
      60,    53,    45,   572,    64,    65,    66,    67,   234,   578,
      77,    51,    45,   623,    74,    75,    68,    24,   623,   701,
      68,   623,   623,     3,     4,    24,    24,    39,   629,     9,
     631,   632,    12,   701,   643,    26,    26,   701,   639,   640,
     641,    27,    26,   644,   732,   522,   620,    26,    26,   650,
      26,   652,   112,   113,   114,   115,   116,    54,   623,   626,
     666,   287,   539,    26,    26,    54,   667,   632,   545,   129,
     671,   131,    27,   673,   639,     8,   641,    26,    74,   526,
     667,    29,   683,   684,   671,    27,    54,    26,    68,    27,
     150,    26,    75,    24,     3,     4,   156,     6,   667,     8,
       9,    29,   671,   245,   705,   165,   166,   708,   168,    33,
     711,   712,    26,    26,    29,    24,   620,    54,    26,   703,
      27,    26,   723,   688,   725,    65,   691,    27,   703,    54,
     688,   732,    29,   691,   701,    26,   737,   738,    26,    29,
     705,    26,    51,   708,    54,   205,   711,   712,    29,   684,
     737,   738,   691,    65,    26,    27,    28,    29,    29,    68,
     220,   221,   763,    29,    33,    51,    24,   644,   737,   738,
     771,    75,    75,   650,   620,   115,    54,    29,   779,    29,
      54,    26,    54,   620,   771,     3,     4,    26,     6,   790,
       8,     9,   802,    26,    27,    28,    29,   802,   763,   800,
     802,   802,   771,   115,    40,   652,    24,    43,    44,    45,
      46,    26,    54,    29,   779,    29,     3,     4,    75,   245,
     785,    54,     9,    54,    29,   790,   166,   785,   168,    33,
     290,    26,    45,    51,   294,   800,   296,   802,    45,   299,
     300,   301,   302,    26,   809,   271,   723,    26,   725,    29,
      68,   809,    54,    29,   166,    29,   168,   317,    29,    29,
      33,   321,   322,   323,    51,   205,    53,    33,    26,    26,
     330,   331,   414,   415,   416,   417,   418,   419,   420,    29,
      29,    68,   729,   343,   344,   732,    54,    56,   765,    34,
      59,    60,   352,   205,    63,    64,    40,    66,    67,    28,
     442,    29,   444,    26,    26,    29,    33,   367,   368,   369,
     370,   371,    28,   373,   374,   375,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    13,   387,   388,   389,
     390,   391,   392,    29,    26,    26,   504,    24,    33,   245,
      26,    26,    54,    26,    58,    29,    60,    54,    29,    29,
      64,    65,    34,    67,    54,    42,    29,    29,    29,    33,
      74,    75,    26,    26,    51,   271,    53,    26,    26,     3,
       4,    26,     6,     7,    26,     9,   402,    33,    54,    29,
      77,    68,   116,   443,   683,    72,    20,   666,   414,   415,
     416,   417,   418,   419,   420,   555,   342,   771,   112,   113,
     114,   115,   428,   429,   115,   431,   432,   433,   434,   435,
     684,   205,   352,   205,   643,   129,   442,   131,   444,    39,
      40,   522,   765,    43,    44,    45,    46,   367,   368,   369,
     370,   371,   504,   373,    68,    69,   150,   763,   779,   790,
     352,   342,   156,   712,   729,    79,   743,   233,   388,   389,
     390,   165,   166,   703,   168,   367,   368,   369,   370,   371,
     629,   373,   522,   129,   632,   333,   526,   299,     3,     4,
     276,   639,     7,   641,     9,   688,   388,   389,   390,   539,
     809,   648,   443,   152,   615,   545,   314,    -1,   455,    24,
      -1,   205,    -1,    -1,    -1,    -1,   402,     3,     4,    -1,
      -1,     7,    -1,     9,    -1,    -1,   220,    -1,   414,   415,
     416,   417,   418,   419,   420,    -1,    51,    -1,    24,    -1,
      -1,    -1,    -1,    -1,    -1,   431,   432,   433,   434,   435,
      -1,    -1,    -1,    68,    -1,   561,   442,   705,   444,    -1,
     708,    -1,   684,   711,    -1,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    -1,    -1,    -1,   504,   505,
     620,    -1,    68,    -1,    -1,    -1,   626,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   290,    -1,    -1,    -1,
     294,    -1,   296,   643,   644,   299,   300,   301,   302,    -1,
     650,    -1,   652,    -1,    -1,   763,    -1,    -1,    -1,   539,
      -1,    -1,    -1,   317,    -1,   545,   666,   321,   322,   323,
      68,   779,    -1,    -1,    72,    -1,   330,   331,    -1,     3,
       4,    -1,   790,     7,    -1,     9,    -1,   539,    -1,   343,
     344,    23,   800,   545,    -1,    -1,    -1,    -1,   352,    -1,
      24,   701,    -1,   703,    36,    37,    38,    -1,    -1,    41,
      -1,    -1,    -1,   367,   368,   369,   370,   371,   684,   373,
     374,   375,    -1,   723,    -1,   725,    -1,    51,    -1,   729,
      -1,    -1,   732,   387,   388,   389,   390,   391,   392,    -1,
      72,    73,    74,    -1,    68,    -1,   632,    -1,    -1,    -1,
      58,    -1,    60,   639,    -1,   641,    64,    65,    66,    67,
      -1,    -1,    -1,    -1,   644,   765,    74,    75,    -1,    -1,
     650,    -1,    -1,    -1,    -1,    -1,    -1,   743,    -1,     3,
       4,     5,     6,     7,     8,     9,    10,    11,    12,   443,
      -1,    -1,   644,    -1,    -1,    -1,    -1,    -1,   650,    -1,
      24,    -1,    -1,    -1,   112,   113,   114,   115,   116,     3,
       4,     5,     6,     7,     8,     9,    10,    11,    12,   705,
      -1,   129,   708,   131,    -1,   711,   712,    -1,    -1,    -1,
      24,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   684,    -1,
       3,     4,   150,   723,    68,   725,     9,    -1,   156,    12,
      -1,    -1,   732,    -1,    -1,    -1,    -1,   165,   166,    -1,
     168,    -1,    -1,   171,    -1,    -1,    -1,    -1,   522,    -1,
      -1,   723,   526,   725,    68,    -1,    -1,   763,    72,    -1,
     732,    -1,    -1,    -1,    -1,   539,    -1,    -1,    51,    -1,
      -1,   545,    -1,   779,    57,    58,    -1,   205,    61,    62,
      -1,    -1,    65,    -1,   790,    68,    -1,    -1,    -1,    -1,
      -1,    -1,   220,   221,   800,     3,     4,     5,    -1,    -1,
       8,     9,    10,    11,    12,   233,    -1,    -1,    -1,    17,
      18,    19,    -1,    21,    22,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    -1,    -1,    -1,    -1,
      -1,    -1,    20,    -1,    -1,    -1,    24,    25,    -1,    -1,
      -1,    -1,    -1,    51,    -1,    53,   620,    26,    27,    28,
      29,    -1,   626,    -1,    42,    34,    -1,    -1,    -1,    -1,
      68,    -1,   290,    51,    52,    53,   294,    -1,   296,   643,
     644,   299,   300,   301,   302,    54,   650,    -1,   652,    -1,
      68,    69,    70,    -1,    72,    -1,    -1,    -1,    76,   317,
      -1,    79,   666,   321,   322,   323,    75,    -1,    77,    78,
      -1,    -1,   330,   331,     3,     4,     5,     6,     7,     8,
       9,    10,    11,    12,    13,   343,   344,    23,    -1,    -1,
      -1,    -1,    -1,    -1,   352,    24,    -1,   701,    -1,   703,
      36,    37,    38,    -1,    -1,    41,    -1,    -1,    -1,   367,
     368,   369,   370,   371,    -1,   373,   374,   375,    -1,   723,
      -1,   725,    -1,    -1,    -1,   729,    -1,    -1,   732,   387,
     388,   389,   390,   391,   392,    -1,    72,    73,    74,    68,
      -1,    -1,    -1,    72,    -1,    -1,    58,    -1,    60,    -1,
      -1,    -1,    64,    65,    -1,    67,    -1,    -1,    -1,    -1,
      -1,   765,    74,    75,    -1,    -1,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    13,    14,    -1,    16,
      -1,    -1,    -1,    20,    -1,   443,    -1,    24,    25,    -1,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
     112,   113,   114,   115,    -1,    42,    43,    44,    -1,    46,
      47,    48,    49,    50,    51,    52,    53,   129,    55,   131,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    68,    69,    70,    -1,    72,    -1,    -1,   150,    76,
      -1,    24,    79,    -1,   156,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   165,   166,    68,   168,    -1,    -1,   171,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   526,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   539,    -1,    -1,    -1,    68,    -1,   545,    -1,    72,
      -1,    -1,    -1,   205,     3,     4,     5,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    15,    16,   220,    -1,
      -1,    20,    -1,    -1,    23,    24,    25,    -1,    -1,    -1,
      -1,   233,    -1,    -1,    -1,    -1,    -1,    36,    37,    38,
      39,    -1,    41,    42,    43,    44,    -1,    46,    47,    48,
      49,    50,    51,    52,    53,    -1,    55,    -1,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    -1,    68,
      69,    70,   620,    72,    73,    74,    -1,    76,   626,    24,
      79,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   290,    -1,
      -1,    -1,   294,    -1,   296,   643,   644,   299,   300,   301,
     302,    -1,   650,    -1,   652,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   317,    -1,    -1,   666,   321,
     322,   323,    -1,    68,    -1,    -1,    -1,    72,   330,   331,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      -1,   343,   344,    -1,    -1,    -1,    -1,    20,    -1,    -1,
     352,    24,    -1,   701,    -1,   703,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   367,   368,   369,   370,   371,
      -1,   373,   374,   375,    -1,   723,    -1,   725,    51,    -1,
      53,   729,    -1,    -1,   732,   387,   388,   389,   390,   391,
     392,    -1,    -1,    -1,    -1,    68,    69,    -1,    -1,    23,
      -1,    -1,    58,    -1,    60,    -1,    -1,    -1,    64,    65,
      -1,    67,    36,    37,    38,    -1,    -1,    41,    74,    75,
      -1,    45,     3,     4,     5,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    -1,    16,    -1,    -1,    -1,    20,
      -1,   443,    -1,    24,    -1,    -1,    -1,    -1,    72,    73,
      74,    -1,    -1,    -1,    -1,    -1,   112,   113,   114,   115,
      -1,    42,    43,    44,    -1,    46,    47,    48,    49,    50,
      51,    -1,    53,   129,    55,   131,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    68,    69,    -1,
      -1,    -1,    -1,    -1,   150,    -1,     3,     4,    79,     6,
     156,     8,     9,    -1,    -1,    -1,    -1,    -1,    -1,    16,
     166,    -1,   168,    -1,    -1,   171,    -1,    24,    -1,    -1,
      -1,    -1,    -1,    -1,   526,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    43,   539,    -1,    -1,
      -1,    -1,    20,   545,    51,    -1,    24,    25,    -1,   205,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    68,    -1,    -1,    42,    -1,    -1,    -1,    -1,    -1,
      -1,    24,    -1,    51,    52,    53,    -1,   233,    -1,    -1,
      -1,    -1,     3,     4,    -1,     6,    -1,     8,     9,    42,
      68,    69,    70,    -1,    72,    16,    -1,    -1,    76,    -1,
      58,    79,    60,    24,    -1,    -1,    64,    65,    -1,    67,
      -1,    -1,    -1,    -1,    -1,    68,    74,    75,   620,    72,
      -1,    -1,    43,    -1,   626,    -1,    -1,    -1,    -1,    -1,
      51,    -1,    -1,    -1,   290,    -1,    -1,    -1,   294,    -1,
     296,   643,   644,   299,   300,   301,   302,    68,   650,    -1,
     652,    -1,    -1,    -1,   112,   113,   114,   115,    -1,    -1,
      -1,   317,    -1,    -1,   666,   321,   322,   323,    -1,    -1,
      -1,   129,    -1,   131,   330,   331,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   150,    -1,    -1,    -1,   352,    -1,   156,   701,
      -1,   703,    -1,    -1,    -1,    -1,    -1,    -1,   166,    -1,
     168,   367,   368,   369,   370,   371,    -1,   373,   374,   375,
      -1,   723,    -1,   725,    -1,    -1,    -1,   729,    -1,    -1,
     732,   387,   388,   389,   390,     3,     4,     5,     6,     7,
      -1,     9,    10,    11,    12,    -1,    14,   205,    58,    -1,
      60,    15,    20,    -1,    64,    65,    24,    67,    -1,    23,
      -1,    25,    -1,    -1,    74,    75,    -1,    -1,    -1,    -1,
      -1,    -1,    36,    37,    38,    39,    44,    41,    -1,    -1,
      48,    49,    50,    51,    -1,    53,    -1,   443,    52,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      68,    69,   112,   113,   114,   115,    70,    -1,    72,    73,
      74,    79,    76,    -1,    -1,    -1,    -1,    -1,    -1,   129,
      -1,   131,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   290,    -1,    -1,    -1,   294,    -1,   296,    -1,
     150,   299,   300,   301,   302,    -1,   156,    -1,    -1,    -1,
      60,    -1,    -1,    -1,    -1,    65,   166,    67,   168,   317,
      -1,   171,    -1,   321,   322,   323,    -1,    -1,    -1,    -1,
     526,    -1,   330,   331,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   539,    -1,    -1,    -1,    -1,    -1,   545,
      -1,    -1,    -1,    -1,   352,   205,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   113,    -1,   115,    -1,    -1,    -1,   367,
     368,   369,   370,   371,    -1,   373,   374,   375,    -1,   129,
      -1,   131,    -1,   233,    -1,    -1,    -1,    -1,    -1,    -1,
     388,   389,   390,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     150,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   166,    -1,   168,    -1,
      -1,    -1,    -1,    -1,   620,    -1,    -1,    -1,    -1,    -1,
     626,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     290,    -1,    -1,    -1,   294,    -1,   296,    -1,   644,   299,
     300,   301,   302,    -1,   650,   205,   652,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   317,    -1,    -1,
      -1,   321,   322,   323,    -1,    -1,    -1,    -1,    -1,    -1,
     330,   331,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   352,    -1,    -1,   701,    -1,   703,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   367,   368,   369,
     370,   371,    -1,   373,   374,   375,    -1,   723,    -1,   725,
      -1,    -1,    -1,   729,    -1,    -1,   732,   387,   388,   389,
     390,   539,    -1,    -1,    -1,    -1,    -1,   545,    -1,     3,
       4,     5,     6,     7,     8,     9,    10,    11,    12,    -1,
      14,    -1,    -1,    -1,    -1,    -1,    20,   317,    -1,    -1,
      24,   321,   322,   323,    -1,    -1,    -1,    -1,    -1,    -1,
     330,   331,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      44,    -1,    -1,   443,    48,    49,    50,    51,    -1,    53,
      -1,    -1,   352,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    68,    69,    -1,   367,   368,   369,
     370,   371,   620,   373,    -1,    -1,    -1,    -1,   626,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   388,   389,
     390,    -1,    -1,    -1,    -1,    -1,   644,    -1,    -1,    -1,
      -1,    -1,   650,    -1,   652,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   526,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   539,
      -1,    -1,    -1,    -1,    -1,   545,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   701,    -1,   703,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   723,    -1,   725,    -1,    -1,
      -1,    -1,    -1,    -1,   732,    -1,    -1,    -1,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      -1,    16,    -1,    -1,    -1,    20,    -1,    -1,    -1,    24,
      25,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     620,    -1,    -1,    -1,    39,    -1,   626,    42,    43,    44,
      -1,    46,    47,    48,    49,    50,    51,    52,    53,   539,
      55,    -1,    -1,    -1,   644,   545,    -1,    -1,    -1,    -1,
     650,    -1,   652,    68,    69,    70,    -1,    72,    -1,    -1,
      -1,    76,    -1,    -1,    79,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     3,     4,     5,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    15,    16,    -1,    -1,    -1,    20,
      -1,    -1,    23,    24,    25,    -1,    -1,    -1,    -1,    -1,
      -1,   701,    -1,   703,    -1,    36,    37,    38,    39,    -1,
      41,    42,    43,    44,    -1,    46,    47,    48,    49,    50,
      51,    52,    53,   723,    55,   725,   626,    -1,    -1,   729,
      -1,    -1,   732,    -1,    -1,    -1,    -1,    68,    69,    70,
      -1,    72,    73,    74,   644,    76,    -1,    -1,    79,    -1,
     650,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,     3,     4,     5,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    -1,    16,    -1,    -1,
      -1,    20,    -1,    -1,    -1,    24,    25,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      39,   701,    -1,    42,    43,    44,    -1,    46,    47,    48,
      49,    50,    51,    52,    53,    -1,    55,    -1,    -1,    -1,
      -1,    -1,    -1,   723,    -1,   725,    -1,    -1,    -1,    68,
      69,    70,   732,    72,    -1,    -1,    -1,    76,    -1,    -1,
      79,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    -1,    16,    -1,    -1,    -1,    20,    -1,
      -1,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    39,    -1,    -1,
      42,    43,    44,    -1,    46,    47,    48,    49,    50,    51,
      52,    53,    -1,    55,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    68,    69,    70,    -1,
      72,    -1,    -1,    -1,    76,    -1,    -1,    79
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int16 yystos[] =
{
       0,    81,    82,    83,     0,    56,    59,    60,    63,    64,
      66,    67,    84,    85,    86,    88,    89,    90,    91,    92,
     302,     3,     4,     9,    12,    68,   315,   316,   317,   318,
     319,   324,   315,   319,   328,   315,   315,   315,   315,    29,
      29,    29,   303,    29,    29,    29,    29,    94,   316,    94,
      51,    77,   304,    27,    94,    94,    94,    94,    29,    30,
      29,   305,   315,    29,    29,    29,    29,    29,     5,     6,
       7,     8,    10,    11,    24,    72,   219,   224,   225,   226,
     227,   228,   229,   230,   231,   232,   233,   234,   236,   237,
     243,   244,   245,   268,   269,   270,   271,   272,   273,   276,
     277,   278,   279,   319,   320,   321,   322,   323,   324,   325,
     326,   327,    17,    18,    19,    21,    22,    51,    53,   276,
     279,   307,   308,   309,   310,   311,   319,   327,    13,    24,
      42,    51,    53,    72,   211,   212,   213,   214,   215,   216,
     217,   218,   219,   220,   221,   222,   224,   238,   239,   253,
     256,    54,    29,   306,   315,    13,    24,   182,   208,   209,
     210,   243,   264,   268,   272,    20,    24,    25,    51,    52,
      53,    69,    70,    76,    79,   144,   145,   146,   147,   148,
     149,   150,   151,   153,   154,   155,   159,   160,   161,   162,
     163,   164,   165,   166,   167,   168,   175,   177,   178,   182,
     194,   195,   196,   201,   207,   251,   252,   253,   256,   264,
     268,   269,   270,   271,   272,   273,   277,   279,    14,    16,
      20,    24,    39,    43,    44,    46,    47,    48,    49,    50,
      51,    53,    55,    69,    95,    96,    97,    98,    99,   100,
     101,   102,   103,   105,   106,   107,   110,   111,   112,   113,
     114,   115,   116,   117,   118,   119,   125,   127,   128,   133,
     135,   137,   138,   139,   140,   141,   142,   143,   197,   207,
     246,   247,   248,   249,   252,   256,   264,   266,   268,   269,
     270,   271,   272,   273,   275,   277,   279,    87,   211,   243,
      24,   224,   236,    15,   265,   266,   267,    29,    93,    74,
      24,    24,    24,   243,   211,   230,   233,   234,   236,   144,
      95,   307,   312,    33,    24,   212,   238,    24,   212,   240,
      93,    74,    23,    23,    36,    37,    38,    41,    72,    73,
      74,   254,    31,   257,    51,   218,   220,   221,   305,    51,
     182,    93,    33,    24,    51,   169,   182,   268,   269,   272,
     273,   145,    24,   145,   176,   178,   179,   268,   272,   277,
     205,   270,   271,   272,   274,    32,    93,    74,    23,    23,
      74,   254,    40,   259,   265,   267,   257,    45,   152,   153,
     160,   161,   162,   166,   178,    51,    35,   250,    24,    24,
      24,    24,    51,   120,   133,   264,    23,    72,    74,    96,
     126,   133,   247,   254,   255,   266,   267,    24,    96,   130,
     268,   272,   205,    93,    74,    23,    45,    23,    45,    74,
     254,   103,   105,   110,   113,   117,   127,   259,   265,   267,
     257,    75,    77,    78,    77,    78,    51,   104,   105,   111,
     112,   117,    33,   250,    45,    24,    24,    24,    93,    26,
     224,   236,   236,    51,    57,    58,    61,    62,    65,    68,
     280,   282,   283,   285,   287,   288,   290,   292,   315,    27,
     245,   235,   236,   235,   235,    26,    26,    26,    26,    26,
     313,    54,   307,   312,    26,    26,   241,    54,    27,   220,
     220,   220,    74,   220,   220,   239,   223,   279,   156,   157,
     158,   279,    26,    27,    24,    51,   183,   184,   185,   187,
     188,   190,   192,   249,   260,   261,   262,   279,   319,   322,
     170,   182,    29,    26,   180,    54,    24,    71,    75,    27,
     151,   153,   159,   166,   151,   151,   151,   151,   176,    24,
     162,   177,   279,   177,   178,    24,   156,   263,   264,   270,
     179,   179,   179,   121,   133,    29,    26,    26,    26,   131,
      54,    24,    71,    27,   103,   103,   103,   103,   103,   103,
     103,    96,    24,   113,   125,   279,   125,   127,    24,   105,
     113,   135,   138,   279,   135,   135,   135,   135,   108,   109,
     279,   102,   103,   105,   134,   135,   136,   138,   263,   103,
     129,   130,   129,   129,    27,    26,   280,   281,   293,   319,
     328,   284,   319,   286,   319,   291,   319,    29,   300,    26,
      29,    26,    26,    29,   314,    26,    29,   242,    54,    29,
      54,    29,    33,   184,   187,   188,   191,   183,   193,    75,
      51,    24,    54,    29,    51,   163,   171,   172,   173,   178,
      29,   181,    79,   162,   195,   202,   203,   204,   206,   145,
     179,    54,    26,    26,    26,    54,    29,    51,    96,   122,
     123,    29,   132,    24,   113,   142,   198,   199,   200,   206,
      96,    96,    54,    29,    33,    26,    26,    26,    29,    54,
      29,    29,   289,    29,    29,   300,   301,   311,   235,   307,
     212,    33,   223,    33,   156,    24,   188,    26,    77,    26,
      26,    77,    29,    54,   188,   156,   188,   189,   170,   163,
     172,   174,   178,    29,    34,   258,   176,   177,    28,    29,
      26,    26,    33,   121,    96,   123,   124,   258,    29,    96,
     247,   266,    28,    29,    26,    26,    33,   108,   134,   281,
     301,   315,    26,   301,   301,    26,   220,   209,   188,   188,
     188,   193,    54,    29,    26,    29,    54,   176,   176,   202,
     151,    29,    54,    96,    96,   198,    29,    29,    29,    33,
     189,   174,    26,   124,    26,    51,    53,   294,   294,   294,
      24,   185,   186,   188,   280,   295,   298,    26,    26,    26,
      24,   190,    33,   299,    54,   296,   187,    26,   307,    29,
     297,   298
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int16 yyr1[] =
{
       0,    80,    81,    82,    83,    83,    84,    84,    85,    85,
      85,    85,    85,    85,    86,    87,    88,    89,    90,    91,
      92,    93,    93,    94,    94,    95,    95,    95,    96,    96,
      96,    96,    96,    96,    97,    97,    97,    98,    99,    99,
      99,   100,   100,   101,   101,   102,   102,   102,   103,   103,
     103,   104,   104,   104,   104,   105,   105,   105,   105,   106,
     107,   108,   108,   109,   110,   110,   111,   112,   113,   113,
     113,   113,   114,   114,   115,   115,   115,   115,   115,   116,
     116,   117,   118,   119,   120,   120,   121,   121,   122,   122,
     123,   124,   124,   125,   125,   125,   126,   126,   126,   126,
     126,   127,   127,   128,   128,   128,   129,   130,   131,   131,
     132,   133,   133,   134,   134,   134,   135,   136,   137,   137,
     137,   138,   138,   139,   139,   140,   140,   141,   142,   143,
     144,   144,   144,   145,   145,   145,   145,   145,   145,   146,
     146,   147,   148,   148,   149,   149,   150,   150,   151,   151,
     151,   152,   152,   152,   152,   153,   153,   153,   153,   154,
     155,   156,   156,   157,   157,   158,   159,   159,   160,   161,
     162,   162,   162,   163,   163,   164,   165,   165,   165,   165,
     166,   167,   167,   168,   169,   169,   170,   170,   171,   171,
     172,   173,   173,   174,   174,   175,   176,   176,   176,   177,
     177,   177,   177,   177,   178,   178,   179,   180,   180,   181,
     182,   182,   183,   183,   184,   184,   184,   185,   186,   186,
     186,   187,   187,   188,   188,   188,   188,   188,   188,   189,
     189,   190,   191,   191,   192,   193,   193,   194,   195,   196,
     197,   197,   198,   198,   199,   199,   200,   201,   201,   202,
     202,   203,   203,   204,   205,   206,   207,   207,   207,   207,
     208,   208,   209,   209,   210,   211,   211,   212,   212,   212,
     213,   213,   214,   215,   215,   216,   216,   217,   217,   218,
     218,   219,   220,   220,   221,   221,   221,   222,   223,   223,
     224,   224,   224,   225,   226,   226,   227,   228,   229,   230,
     230,   231,   231,   232,   233,   233,   234,   234,   235,   235,
     236,   236,   237,   237,   237,   238,   238,   239,   239,   240,
     241,   241,   242,   243,   243,   244,   244,   245,   245,   245,
     245,   246,   246,   246,   247,   247,   248,   248,   248,   249,
     249,   250,   251,   251,   252,   252,   253,   253,   254,   254,
     254,   254,   254,   254,   255,   255,   256,   257,   258,   259,
     260,   261,   262,   263,   263,   264,   264,   265,   266,   267,
     268,   269,   270,   271,   272,   273,   274,   274,   275,   275,
     275,   275,   275,   276,   277,   277,   278,   279,   280,   280,
     280,   280,   280,   281,   281,   282,   282,   283,   284,   285,
     286,   287,   287,   287,   288,   289,   289,   290,   291,   292,
     293,   294,   294,   295,   296,   296,   297,   298,   299,   299,
     300,   300,   301,   302,   303,   303,   303,   304,   304,   305,
     305,   306,   307,   307,   307,   308,   308,   308,   308,   308,
     308,   309,   310,   310,   310,   310,   310,   311,   311,   312,
     313,   313,   314,   315,   315,   316,   316,   317,   318,   319,
     319,   319,   320,   321,   322,   323,   324,   325,   326,   327,
     327,   327,   328
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     1,     1,     0,     2,     1,     1,     1,     1,
       1,     1,     1,     1,     8,     1,     8,     8,     8,     8,
       8,     3,     0,     1,     3,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     3,     1,     1,
       1,     3,     3,     3,     3,     3,     3,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     3,     2,
       5,     1,     3,     3,     1,     1,     2,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     3,     1,     1,     1,
       1,     3,     1,     7,     1,     3,     1,     3,     1,     3,
       3,     1,     3,     1,     1,     3,     1,     1,     1,     1,
       1,     1,     3,     4,     4,     4,     1,     2,     0,     2,
       2,     3,     3,     1,     1,     1,     1,     1,     1,     1,
       1,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     3,     1,     1,     3,     3,     3,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     3,     1,
       6,     1,     3,     1,     1,     3,     1,     1,     2,     3,
       1,     1,     1,     1,     4,     1,     1,     4,     1,     1,
       3,     1,     4,     7,     1,     3,     1,     3,     1,     3,
       3,     1,     1,     1,     3,     5,     1,     1,     1,     1,
       1,     1,     1,     3,     1,     3,     2,     0,     2,     2,
       3,     3,     1,     1,     1,     1,     3,     6,     1,     3,
       1,     1,     3,     1,     1,     1,     4,     3,     1,     1,
       3,     3,     3,     3,     3,     1,     3,     3,     3,     3,
       3,     5,     1,     3,     1,     1,     1,     3,     5,     1,
       3,     1,     1,     1,     1,     2,     1,     3,     1,     1,
       1,     1,     1,     1,     6,     1,     1,     1,     1,     1,
       1,     1,     3,     1,     1,     3,     3,     3,     3,     2,
       1,     3,     1,     1,     1,     1,     3,     6,     1,     3,
       1,     1,     1,     1,     1,     1,     1,     3,     1,     1,
       4,     1,     1,     1,     1,     4,     1,     4,     1,     3,
       1,     1,     1,     1,     1,     3,     3,     1,     3,     2,
       0,     2,     2,     1,     3,     1,     3,     1,     2,     4,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     2,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     3,     1,     3,     1,     1,     7,     1,     7,
       1,     1,     1,     1,     4,     2,     0,     4,     1,     7,
       1,     1,     3,     2,     0,     2,     2,     2,     2,     0,
       2,     0,     1,     4,     0,     2,     4,     3,     1,     1,
       3,     1,     1,     3,     1,     1,     1,     1,     1,     1,
       1,     4,     3,     3,     3,     3,     3,     1,     3,     2,
       0,     2,     2,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = TOK_YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == TOK_YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (scanner, context, YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use TOK_YYerror or TOK_YYUNDEF. */
#define YYERRCODE TOK_YYUNDEF


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)




# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value, scanner, context); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, yyscan_t scanner, TptpParseContext *context)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  YY_USE (scanner);
  YY_USE (context);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, yyscan_t scanner, TptpParseContext *context)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  yy_symbol_value_print (yyo, yykind, yyvaluep, scanner, context);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp,
                 int yyrule, yyscan_t scanner, TptpParseContext *context)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)], scanner, context);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule, scanner, context); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif






/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep, yyscan_t scanner, TptpParseContext *context)
{
  YY_USE (yyvaluep);
  YY_USE (scanner);
  YY_USE (context);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  switch (yykind)
    {
    case YYSYMBOL_SINGLE_QUOTED: /* SINGLE_QUOTED  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2333 "parser.tab.c"
        break;

    case YYSYMBOL_BACK_QUOTED: /* BACK_QUOTED  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2339 "parser.tab.c"
        break;

    case YYSYMBOL_DISTINCT_OBJECT: /* DISTINCT_OBJECT  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2345 "parser.tab.c"
        break;

    case YYSYMBOL_DOLLAR_WORD: /* DOLLAR_WORD  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2351 "parser.tab.c"
        break;

    case YYSYMBOL_DOLLAR_DOLLAR_WORD: /* DOLLAR_DOLLAR_WORD  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2357 "parser.tab.c"
        break;

    case YYSYMBOL_UPPER_WORD: /* UPPER_WORD  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2363 "parser.tab.c"
        break;

    case YYSYMBOL_LOWER_WORD: /* LOWER_WORD  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2369 "parser.tab.c"
        break;

    case YYSYMBOL_REAL: /* REAL  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2375 "parser.tab.c"
        break;

    case YYSYMBOL_RATIONAL: /* RATIONAL  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2381 "parser.tab.c"
        break;

    case YYSYMBOL_INTEGER: /* INTEGER  */
#line 433 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2387 "parser.tab.c"
        break;

    case YYSYMBOL_tptp_file: /* tptp_file  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2393 "parser.tab.c"
        break;

    case YYSYMBOL_tptp_input_list: /* tptp_input_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2399 "parser.tab.c"
        break;

    case YYSYMBOL_tptp_input: /* tptp_input  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2405 "parser.tab.c"
        break;

    case YYSYMBOL_annotated_formula: /* annotated_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2411 "parser.tab.c"
        break;

    case YYSYMBOL_tpi_annotated: /* tpi_annotated  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2417 "parser.tab.c"
        break;

    case YYSYMBOL_tpi_formula: /* tpi_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2423 "parser.tab.c"
        break;

    case YYSYMBOL_thf_annotated: /* thf_annotated  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2429 "parser.tab.c"
        break;

    case YYSYMBOL_tff_annotated: /* tff_annotated  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2435 "parser.tab.c"
        break;

    case YYSYMBOL_tcf_annotated: /* tcf_annotated  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2441 "parser.tab.c"
        break;

    case YYSYMBOL_fof_annotated: /* fof_annotated  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2447 "parser.tab.c"
        break;

    case YYSYMBOL_cnf_annotated: /* cnf_annotated  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2453 "parser.tab.c"
        break;

    case YYSYMBOL_annotations: /* annotations  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2459 "parser.tab.c"
        break;

    case YYSYMBOL_formula_role: /* formula_role  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2465 "parser.tab.c"
        break;

    case YYSYMBOL_thf_formula: /* thf_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2471 "parser.tab.c"
        break;

    case YYSYMBOL_thf_logic_formula: /* thf_logic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2477 "parser.tab.c"
        break;

    case YYSYMBOL_thf_binary_formula: /* thf_binary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2483 "parser.tab.c"
        break;

    case YYSYMBOL_thf_binary_nonassoc: /* thf_binary_nonassoc  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2489 "parser.tab.c"
        break;

    case YYSYMBOL_thf_binary_assoc: /* thf_binary_assoc  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2495 "parser.tab.c"
        break;

    case YYSYMBOL_thf_or_formula: /* thf_or_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2501 "parser.tab.c"
        break;

    case YYSYMBOL_thf_and_formula: /* thf_and_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2507 "parser.tab.c"
        break;

    case YYSYMBOL_thf_apply_formula: /* thf_apply_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2513 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unit_formula: /* thf_unit_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2519 "parser.tab.c"
        break;

    case YYSYMBOL_thf_preunit_formula: /* thf_preunit_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2525 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unitary_formula: /* thf_unitary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2531 "parser.tab.c"
        break;

    case YYSYMBOL_thf_quantified_formula: /* thf_quantified_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2537 "parser.tab.c"
        break;

    case YYSYMBOL_thf_quantification: /* thf_quantification  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2543 "parser.tab.c"
        break;

    case YYSYMBOL_thf_variable_list: /* thf_variable_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2549 "parser.tab.c"
        break;

    case YYSYMBOL_thf_typed_variable: /* thf_typed_variable  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2555 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unary_formula: /* thf_unary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2561 "parser.tab.c"
        break;

    case YYSYMBOL_thf_prefix_unary: /* thf_prefix_unary  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2567 "parser.tab.c"
        break;

    case YYSYMBOL_thf_infix_unary: /* thf_infix_unary  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2573 "parser.tab.c"
        break;

    case YYSYMBOL_thf_atomic_formula: /* thf_atomic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2579 "parser.tab.c"
        break;

    case YYSYMBOL_thf_plain_atomic: /* thf_plain_atomic  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2585 "parser.tab.c"
        break;

    case YYSYMBOL_thf_defined_atomic: /* thf_defined_atomic  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2591 "parser.tab.c"
        break;

    case YYSYMBOL_thf_defined_term: /* thf_defined_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2597 "parser.tab.c"
        break;

    case YYSYMBOL_thf_defined_infix: /* thf_defined_infix  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2603 "parser.tab.c"
        break;

    case YYSYMBOL_thf_system_atomic: /* thf_system_atomic  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2609 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let: /* thf_let  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2615 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let_types: /* thf_let_types  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2621 "parser.tab.c"
        break;

    case YYSYMBOL_thf_atom_typing_list: /* thf_atom_typing_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2627 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let_defns: /* thf_let_defns  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2633 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let_defn: /* thf_let_defn  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2639 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let_defn_list: /* thf_let_defn_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2645 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unitary_term: /* thf_unitary_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2651 "parser.tab.c"
        break;

    case YYSYMBOL_thf_conn_term: /* thf_conn_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2657 "parser.tab.c"
        break;

    case YYSYMBOL_thf_tuple: /* thf_tuple  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2663 "parser.tab.c"
        break;

    case YYSYMBOL_thf_fof_function: /* thf_fof_function  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2669 "parser.tab.c"
        break;

    case YYSYMBOL_thf_arguments: /* thf_arguments  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2675 "parser.tab.c"
        break;

    case YYSYMBOL_thf_formula_list: /* thf_formula_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2681 "parser.tab.c"
        break;

    case YYSYMBOL_comma_thf_logic_formula_list: /* comma_thf_logic_formula_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2687 "parser.tab.c"
        break;

    case YYSYMBOL_comma_thf_logic_formula: /* comma_thf_logic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2693 "parser.tab.c"
        break;

    case YYSYMBOL_thf_atom_typing: /* thf_atom_typing  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2699 "parser.tab.c"
        break;

    case YYSYMBOL_thf_top_level_type: /* thf_top_level_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2705 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unitary_type: /* thf_unitary_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2711 "parser.tab.c"
        break;

    case YYSYMBOL_thf_apply_type: /* thf_apply_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2717 "parser.tab.c"
        break;

    case YYSYMBOL_thf_binary_type: /* thf_binary_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2723 "parser.tab.c"
        break;

    case YYSYMBOL_thf_mapping_type: /* thf_mapping_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2729 "parser.tab.c"
        break;

    case YYSYMBOL_thf_xprod_type: /* thf_xprod_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2735 "parser.tab.c"
        break;

    case YYSYMBOL_thf_union_type: /* thf_union_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2741 "parser.tab.c"
        break;

    case YYSYMBOL_thf_subtype: /* thf_subtype  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2747 "parser.tab.c"
        break;

    case YYSYMBOL_thf_definition: /* thf_definition  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2753 "parser.tab.c"
        break;

    case YYSYMBOL_thf_sequent: /* thf_sequent  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2759 "parser.tab.c"
        break;

    case YYSYMBOL_tff_formula: /* tff_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2765 "parser.tab.c"
        break;

    case YYSYMBOL_tff_logic_formula: /* tff_logic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2771 "parser.tab.c"
        break;

    case YYSYMBOL_tff_binary_formula: /* tff_binary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2777 "parser.tab.c"
        break;

    case YYSYMBOL_tff_binary_nonassoc: /* tff_binary_nonassoc  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2783 "parser.tab.c"
        break;

    case YYSYMBOL_tff_binary_assoc: /* tff_binary_assoc  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2789 "parser.tab.c"
        break;

    case YYSYMBOL_tff_or_formula: /* tff_or_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2795 "parser.tab.c"
        break;

    case YYSYMBOL_tff_and_formula: /* tff_and_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2801 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unit_formula: /* tff_unit_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2807 "parser.tab.c"
        break;

    case YYSYMBOL_tff_preunit_formula: /* tff_preunit_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2813 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unitary_formula: /* tff_unitary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2819 "parser.tab.c"
        break;

    case YYSYMBOL_txf_unitary_formula: /* txf_unitary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2825 "parser.tab.c"
        break;

    case YYSYMBOL_tff_quantified_formula: /* tff_quantified_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2831 "parser.tab.c"
        break;

    case YYSYMBOL_tff_variable_list: /* tff_variable_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2837 "parser.tab.c"
        break;

    case YYSYMBOL_tff_variable: /* tff_variable  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2843 "parser.tab.c"
        break;

    case YYSYMBOL_tff_typed_variable: /* tff_typed_variable  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2849 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unary_formula: /* tff_unary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2855 "parser.tab.c"
        break;

    case YYSYMBOL_tff_prefix_unary: /* tff_prefix_unary  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2861 "parser.tab.c"
        break;

    case YYSYMBOL_tff_infix_unary: /* tff_infix_unary  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2867 "parser.tab.c"
        break;

    case YYSYMBOL_tff_atomic_formula: /* tff_atomic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2873 "parser.tab.c"
        break;

    case YYSYMBOL_tff_plain_atomic: /* tff_plain_atomic  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2879 "parser.tab.c"
        break;

    case YYSYMBOL_tff_defined_atomic: /* tff_defined_atomic  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2885 "parser.tab.c"
        break;

    case YYSYMBOL_tff_defined_plain: /* tff_defined_plain  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2891 "parser.tab.c"
        break;

    case YYSYMBOL_tff_defined_infix: /* tff_defined_infix  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2897 "parser.tab.c"
        break;

    case YYSYMBOL_tff_system_atomic: /* tff_system_atomic  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2903 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let: /* txf_let  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2909 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_types: /* txf_let_types  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2915 "parser.tab.c"
        break;

    case YYSYMBOL_tff_atom_typing_list: /* tff_atom_typing_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2921 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_defns: /* txf_let_defns  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2927 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_defn: /* txf_let_defn  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2933 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_LHS: /* txf_let_LHS  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2939 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_defn_list: /* txf_let_defn_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2945 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_atom: /* nxf_atom  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2951 "parser.tab.c"
        break;

    case YYSYMBOL_tff_term: /* tff_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2957 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unitary_term: /* tff_unitary_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2963 "parser.tab.c"
        break;

    case YYSYMBOL_txf_tuple: /* txf_tuple  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2969 "parser.tab.c"
        break;

    case YYSYMBOL_tff_arguments: /* tff_arguments  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2975 "parser.tab.c"
        break;

    case YYSYMBOL_comma_tff_term_list: /* comma_tff_term_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2981 "parser.tab.c"
        break;

    case YYSYMBOL_comma_tff_term: /* comma_tff_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2987 "parser.tab.c"
        break;

    case YYSYMBOL_tff_atom_typing: /* tff_atom_typing  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2993 "parser.tab.c"
        break;

    case YYSYMBOL_tff_top_level_type: /* tff_top_level_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2999 "parser.tab.c"
        break;

    case YYSYMBOL_tff_non_atomic_type: /* tff_non_atomic_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3005 "parser.tab.c"
        break;

    case YYSYMBOL_tf1_quantified_type: /* tf1_quantified_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3011 "parser.tab.c"
        break;

    case YYSYMBOL_tff_monotype: /* tff_monotype  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3017 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unitary_type: /* tff_unitary_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3023 "parser.tab.c"
        break;

    case YYSYMBOL_tff_atomic_type: /* tff_atomic_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3029 "parser.tab.c"
        break;

    case YYSYMBOL_tff_type_arguments: /* tff_type_arguments  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3035 "parser.tab.c"
        break;

    case YYSYMBOL_tff_mapping_type: /* tff_mapping_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3041 "parser.tab.c"
        break;

    case YYSYMBOL_tff_xprod_type: /* tff_xprod_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3047 "parser.tab.c"
        break;

    case YYSYMBOL_txf_tuple_type: /* txf_tuple_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3053 "parser.tab.c"
        break;

    case YYSYMBOL_tff_type_list: /* tff_type_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3059 "parser.tab.c"
        break;

    case YYSYMBOL_tff_subtype: /* tff_subtype  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3065 "parser.tab.c"
        break;

    case YYSYMBOL_txf_definition: /* txf_definition  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3071 "parser.tab.c"
        break;

    case YYSYMBOL_txf_sequent: /* txf_sequent  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3077 "parser.tab.c"
        break;

    case YYSYMBOL_nhf_long_connective: /* nhf_long_connective  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3083 "parser.tab.c"
        break;

    case YYSYMBOL_nhf_parameter_list: /* nhf_parameter_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3089 "parser.tab.c"
        break;

    case YYSYMBOL_nhf_parameter: /* nhf_parameter  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3095 "parser.tab.c"
        break;

    case YYSYMBOL_nhf_key_pair: /* nhf_key_pair  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3101 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_long_connective: /* nxf_long_connective  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3107 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_parameter_list: /* nxf_parameter_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3113 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_parameter: /* nxf_parameter  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3119 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_key_pair: /* nxf_key_pair  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3125 "parser.tab.c"
        break;

    case YYSYMBOL_ntf_connective_name: /* ntf_connective_name  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3131 "parser.tab.c"
        break;

    case YYSYMBOL_ntf_index: /* ntf_index  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3137 "parser.tab.c"
        break;

    case YYSYMBOL_ntf_short_connective: /* ntf_short_connective  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3143 "parser.tab.c"
        break;

    case YYSYMBOL_tcf_formula: /* tcf_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3149 "parser.tab.c"
        break;

    case YYSYMBOL_tcf_logic_formula: /* tcf_logic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3155 "parser.tab.c"
        break;

    case YYSYMBOL_tcf_quantified_formula: /* tcf_quantified_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3161 "parser.tab.c"
        break;

    case YYSYMBOL_fof_formula: /* fof_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3167 "parser.tab.c"
        break;

    case YYSYMBOL_fof_logic_formula: /* fof_logic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3173 "parser.tab.c"
        break;

    case YYSYMBOL_fof_binary_formula: /* fof_binary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3179 "parser.tab.c"
        break;

    case YYSYMBOL_fof_binary_nonassoc: /* fof_binary_nonassoc  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3185 "parser.tab.c"
        break;

    case YYSYMBOL_fof_binary_assoc: /* fof_binary_assoc  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3191 "parser.tab.c"
        break;

    case YYSYMBOL_fof_or_formula: /* fof_or_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3197 "parser.tab.c"
        break;

    case YYSYMBOL_fof_and_formula: /* fof_and_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3203 "parser.tab.c"
        break;

    case YYSYMBOL_fof_unary_formula: /* fof_unary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3209 "parser.tab.c"
        break;

    case YYSYMBOL_fof_infix_unary: /* fof_infix_unary  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3215 "parser.tab.c"
        break;

    case YYSYMBOL_fof_unit_formula: /* fof_unit_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3221 "parser.tab.c"
        break;

    case YYSYMBOL_fof_unitary_formula: /* fof_unitary_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3227 "parser.tab.c"
        break;

    case YYSYMBOL_fof_quantified_formula: /* fof_quantified_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3233 "parser.tab.c"
        break;

    case YYSYMBOL_fof_variable_list: /* fof_variable_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3239 "parser.tab.c"
        break;

    case YYSYMBOL_fof_atomic_formula: /* fof_atomic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3245 "parser.tab.c"
        break;

    case YYSYMBOL_fof_plain_atomic_formula: /* fof_plain_atomic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3251 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_atomic_formula: /* fof_defined_atomic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3257 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_plain_formula: /* fof_defined_plain_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3263 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_infix_formula: /* fof_defined_infix_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3269 "parser.tab.c"
        break;

    case YYSYMBOL_fof_system_atomic_formula: /* fof_system_atomic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3275 "parser.tab.c"
        break;

    case YYSYMBOL_fof_plain_term: /* fof_plain_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3281 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_term: /* fof_defined_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3287 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_atomic_term: /* fof_defined_atomic_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3293 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_plain_term: /* fof_defined_plain_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3299 "parser.tab.c"
        break;

    case YYSYMBOL_fof_system_term: /* fof_system_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3305 "parser.tab.c"
        break;

    case YYSYMBOL_fof_arguments: /* fof_arguments  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3311 "parser.tab.c"
        break;

    case YYSYMBOL_fof_term: /* fof_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3317 "parser.tab.c"
        break;

    case YYSYMBOL_fof_function_term: /* fof_function_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3323 "parser.tab.c"
        break;

    case YYSYMBOL_fof_sequent: /* fof_sequent  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3329 "parser.tab.c"
        break;

    case YYSYMBOL_fof_formula_tuple: /* fof_formula_tuple  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3335 "parser.tab.c"
        break;

    case YYSYMBOL_fof_formula_tuple_list: /* fof_formula_tuple_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3341 "parser.tab.c"
        break;

    case YYSYMBOL_comma_fof_logic_formula_list: /* comma_fof_logic_formula_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3347 "parser.tab.c"
        break;

    case YYSYMBOL_comma_fof_logic_formula: /* comma_fof_logic_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3353 "parser.tab.c"
        break;

    case YYSYMBOL_cnf_formula: /* cnf_formula  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3359 "parser.tab.c"
        break;

    case YYSYMBOL_cnf_disjunction: /* cnf_disjunction  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3365 "parser.tab.c"
        break;

    case YYSYMBOL_cnf_literal: /* cnf_literal  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3371 "parser.tab.c"
        break;

    case YYSYMBOL_thf_quantifier: /* thf_quantifier  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3377 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unary_connective: /* thf_unary_connective  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3383 "parser.tab.c"
        break;

    case YYSYMBOL_th0_quantifier: /* th0_quantifier  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3389 "parser.tab.c"
        break;

    case YYSYMBOL_type_quantifier: /* type_quantifier  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3395 "parser.tab.c"
        break;

    case YYSYMBOL_subtype_sign: /* subtype_sign  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3401 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unary_connective: /* tff_unary_connective  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3407 "parser.tab.c"
        break;

    case YYSYMBOL_tff_quantifier: /* tff_quantifier  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3413 "parser.tab.c"
        break;

    case YYSYMBOL_fof_quantifier: /* fof_quantifier  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3419 "parser.tab.c"
        break;

    case YYSYMBOL_nonassoc_connective: /* nonassoc_connective  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3425 "parser.tab.c"
        break;

    case YYSYMBOL_assoc_connective: /* assoc_connective  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3431 "parser.tab.c"
        break;

    case YYSYMBOL_unary_connective: /* unary_connective  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3437 "parser.tab.c"
        break;

    case YYSYMBOL_gentzen_arrow: /* gentzen_arrow  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3443 "parser.tab.c"
        break;

    case YYSYMBOL_assignment: /* assignment  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3449 "parser.tab.c"
        break;

    case YYSYMBOL_identical: /* identical  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3455 "parser.tab.c"
        break;

    case YYSYMBOL_type_constant: /* type_constant  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3461 "parser.tab.c"
        break;

    case YYSYMBOL_type_functor: /* type_functor  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3467 "parser.tab.c"
        break;

    case YYSYMBOL_defined_type: /* defined_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3473 "parser.tab.c"
        break;

    case YYSYMBOL_atom: /* atom  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3479 "parser.tab.c"
        break;

    case YYSYMBOL_untyped_atom: /* untyped_atom  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3485 "parser.tab.c"
        break;

    case YYSYMBOL_defined_infix_pred: /* defined_infix_pred  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3491 "parser.tab.c"
        break;

    case YYSYMBOL_infix_equality: /* infix_equality  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3497 "parser.tab.c"
        break;

    case YYSYMBOL_infix_inequality: /* infix_inequality  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3503 "parser.tab.c"
        break;

    case YYSYMBOL_constant: /* constant  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3509 "parser.tab.c"
        break;

    case YYSYMBOL_functor: /* functor  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3515 "parser.tab.c"
        break;

    case YYSYMBOL_defined_constant: /* defined_constant  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3521 "parser.tab.c"
        break;

    case YYSYMBOL_defined_functor: /* defined_functor  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3527 "parser.tab.c"
        break;

    case YYSYMBOL_system_constant: /* system_constant  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3533 "parser.tab.c"
        break;

    case YYSYMBOL_system_functor: /* system_functor  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3539 "parser.tab.c"
        break;

    case YYSYMBOL_def_or_sys_constant: /* def_or_sys_constant  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3545 "parser.tab.c"
        break;

    case YYSYMBOL_th1_defined_term: /* th1_defined_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3551 "parser.tab.c"
        break;

    case YYSYMBOL_distinct_object: /* distinct_object  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3557 "parser.tab.c"
        break;

    case YYSYMBOL_defined_term: /* defined_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3563 "parser.tab.c"
        break;

    case YYSYMBOL_upper_word: /* upper_word  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3569 "parser.tab.c"
        break;

    case YYSYMBOL_variable: /* variable  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3575 "parser.tab.c"
        break;

    case YYSYMBOL_source: /* source  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3581 "parser.tab.c"
        break;

    case YYSYMBOL_sources: /* sources  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3587 "parser.tab.c"
        break;

    case YYSYMBOL_dag_source: /* dag_source  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3593 "parser.tab.c"
        break;

    case YYSYMBOL_inference_record: /* inference_record  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3599 "parser.tab.c"
        break;

    case YYSYMBOL_inference_rule: /* inference_rule  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3605 "parser.tab.c"
        break;

    case YYSYMBOL_internal_source: /* internal_source  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3611 "parser.tab.c"
        break;

    case YYSYMBOL_intro_type: /* intro_type  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3617 "parser.tab.c"
        break;

    case YYSYMBOL_external_source: /* external_source  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3623 "parser.tab.c"
        break;

    case YYSYMBOL_file_source: /* file_source  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3629 "parser.tab.c"
        break;

    case YYSYMBOL_file_info: /* file_info  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3635 "parser.tab.c"
        break;

    case YYSYMBOL_theory: /* theory  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3641 "parser.tab.c"
        break;

    case YYSYMBOL_theory_name: /* theory_name  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3647 "parser.tab.c"
        break;

    case YYSYMBOL_creator_source: /* creator_source  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3653 "parser.tab.c"
        break;

    case YYSYMBOL_creator_name: /* creator_name  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3659 "parser.tab.c"
        break;

    case YYSYMBOL_parents: /* parents  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3665 "parser.tab.c"
        break;

    case YYSYMBOL_parent_list: /* parent_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3671 "parser.tab.c"
        break;

    case YYSYMBOL_comma_parent_info_list: /* comma_parent_info_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3677 "parser.tab.c"
        break;

    case YYSYMBOL_comma_parent_info: /* comma_parent_info  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3683 "parser.tab.c"
        break;

    case YYSYMBOL_parent_info: /* parent_info  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3689 "parser.tab.c"
        break;

    case YYSYMBOL_parent_details: /* parent_details  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3695 "parser.tab.c"
        break;

    case YYSYMBOL_optional_info: /* optional_info  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3701 "parser.tab.c"
        break;

    case YYSYMBOL_useful_info: /* useful_info  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3707 "parser.tab.c"
        break;

    case YYSYMBOL_include: /* include  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3713 "parser.tab.c"
        break;

    case YYSYMBOL_include_optionals: /* include_optionals  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3719 "parser.tab.c"
        break;

    case YYSYMBOL_formula_selection: /* formula_selection  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3725 "parser.tab.c"
        break;

    case YYSYMBOL_name_list: /* name_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3731 "parser.tab.c"
        break;

    case YYSYMBOL_space_name: /* space_name  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3737 "parser.tab.c"
        break;

    case YYSYMBOL_general_term: /* general_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3743 "parser.tab.c"
        break;

    case YYSYMBOL_general_data: /* general_data  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3749 "parser.tab.c"
        break;

    case YYSYMBOL_general_function: /* general_function  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3755 "parser.tab.c"
        break;

    case YYSYMBOL_formula_data: /* formula_data  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3761 "parser.tab.c"
        break;

    case YYSYMBOL_general_list: /* general_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3767 "parser.tab.c"
        break;

    case YYSYMBOL_general_terms: /* general_terms  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3773 "parser.tab.c"
        break;

    case YYSYMBOL_comma_general_term_list: /* comma_general_term_list  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3779 "parser.tab.c"
        break;

    case YYSYMBOL_comma_general_term: /* comma_general_term  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3785 "parser.tab.c"
        break;

    case YYSYMBOL_name: /* name  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3791 "parser.tab.c"
        break;

    case YYSYMBOL_lower_word: /* lower_word  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3797 "parser.tab.c"
        break;

    case YYSYMBOL_single_quoted: /* single_quoted  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3803 "parser.tab.c"
        break;

    case YYSYMBOL_back_quoted: /* back_quoted  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3809 "parser.tab.c"
        break;

    case YYSYMBOL_atomic_word: /* atomic_word  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3815 "parser.tab.c"
        break;

    case YYSYMBOL_dollar_word: /* dollar_word  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3821 "parser.tab.c"
        break;

    case YYSYMBOL_dollar_dollar_word: /* dollar_dollar_word  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3827 "parser.tab.c"
        break;

    case YYSYMBOL_atomic_defined_word: /* atomic_defined_word  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3833 "parser.tab.c"
        break;

    case YYSYMBOL_atomic_system_word: /* atomic_system_word  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3839 "parser.tab.c"
        break;

    case YYSYMBOL_integer: /* integer  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3845 "parser.tab.c"
        break;

    case YYSYMBOL_rational: /* rational  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3851 "parser.tab.c"
        break;

    case YYSYMBOL_real: /* real  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3857 "parser.tab.c"
        break;

    case YYSYMBOL_number: /* number  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3863 "parser.tab.c"
        break;

    case YYSYMBOL_file_name: /* file_name  */
#line 434 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3869 "parser.tab.c"
        break;

      default:
        break;
    }
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}






/*----------.
| yyparse.  |
`----------*/

int
yyparse (yyscan_t scanner, TptpParseContext *context)
{
/* Lookahead token kind.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

    /* Number of syntax errors so far.  */
    int yynerrs = 0;

    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = TOK_YYEMPTY; /* Cause a token to be read.  */

  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == TOK_YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex (&yylval, scanner);
    }

  if (yychar <= TOK_YYEOF)
    {
      yychar = TOK_YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == TOK_YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = TOK_YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  /* Discard the shifted token.  */
  yychar = TOK_YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 2: /* start: tptp_file  */
#line 441 "parser.y"
            { context->result = (yyvsp[0].data); }
#line 4145 "parser.tab.c"
    break;

  case 3: /* tptp_file: tptp_input_list  */
#line 445 "parser.y"
                  { (yyval.data) = Tptp_mk_TptpFile_mk(lean_array_to_list((yyvsp[0].data))); }
#line 4151 "parser.tab.c"
    break;

  case 4: /* tptp_input_list: %empty  */
#line 449 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 4157 "parser.tab.c"
    break;

  case 5: /* tptp_input_list: tptp_input_list tptp_input  */
#line 450 "parser.y"
                               { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4163 "parser.tab.c"
    break;

  case 6: /* tptp_input: annotated_formula  */
#line 454 "parser.y"
                    { (yyval.data) = Tptp_mk_TptpInput_annotatedFormula((yyvsp[0].data)); }
#line 4169 "parser.tab.c"
    break;

  case 7: /* tptp_input: include  */
#line 455 "parser.y"
            { (yyval.data) = Tptp_mk_TptpInput_include((yyvsp[0].data)); }
#line 4175 "parser.tab.c"
    break;

  case 8: /* annotated_formula: thf_annotated  */
#line 459 "parser.y"
                { (yyval.data) = Tptp_mk_AnnotatedFormula_thfAnnotated((yyvsp[0].data)); }
#line 4181 "parser.tab.c"
    break;

  case 9: /* annotated_formula: tff_annotated  */
#line 460 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_tffAnnotated((yyvsp[0].data)); }
#line 4187 "parser.tab.c"
    break;

  case 10: /* annotated_formula: tcf_annotated  */
#line 461 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_tcfAnnotated((yyvsp[0].data)); }
#line 4193 "parser.tab.c"
    break;

  case 11: /* annotated_formula: fof_annotated  */
#line 462 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_fofAnnotated((yyvsp[0].data)); }
#line 4199 "parser.tab.c"
    break;

  case 12: /* annotated_formula: cnf_annotated  */
#line 463 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_cnfAnnotated((yyvsp[0].data)); }
#line 4205 "parser.tab.c"
    break;

  case 13: /* annotated_formula: tpi_annotated  */
#line 464 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_tpiAnnotated((yyvsp[0].data)); }
#line 4211 "parser.tab.c"
    break;

  case 14: /* tpi_annotated: "tpi(" name "," formula_role "," tpi_formula annotations ")."  */
#line 468 "parser.y"
                                                                { (yyval.data) = Tptp_mk_TpiAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4217 "parser.tab.c"
    break;

  case 15: /* tpi_formula: fof_formula  */
#line 472 "parser.y"
              { (yyval.data) = Tptp_mk_TpiFormula_mk((yyvsp[0].data)); }
#line 4223 "parser.tab.c"
    break;

  case 16: /* thf_annotated: "thf(" name "," formula_role "," thf_formula annotations ")."  */
#line 476 "parser.y"
                                                                { (yyval.data) = Tptp_mk_ThfAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4229 "parser.tab.c"
    break;

  case 17: /* tff_annotated: "tff(" name "," formula_role "," tff_formula annotations ")."  */
#line 480 "parser.y"
                                                                { (yyval.data) = Tptp_mk_TffAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4235 "parser.tab.c"
    break;

  case 18: /* tcf_annotated: "tcf(" name "," formula_role "," tcf_formula annotations ")."  */
#line 484 "parser.y"
                                                                { (yyval.data) = Tptp_mk_TcfAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4241 "parser.tab.c"
    break;

  case 19: /* fof_annotated: "fof(" name "," formula_role "," fof_formula annotations ")."  */
#line 488 "parser.y"
                                                                { (yyval.data) = Tptp_mk_FofAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4247 "parser.tab.c"
    break;

  case 20: /* cnf_annotated: "cnf(" name "," formula_role "," cnf_formula annotations ")."  */
#line 492 "parser.y"
                                                                { (yyval.data) = Tptp_mk_CnfAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4253 "parser.tab.c"
    break;

  case 21: /* annotations: "," source optional_info  */
#line 496 "parser.y"
                           { (yyval.data) = Tptp_mk_Annotations_sourceOptionalInfo((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4259 "parser.tab.c"
    break;

  case 22: /* annotations: %empty  */
#line 497 "parser.y"
           { (yyval.data) = Tptp_mk_Annotations_nothing; }
#line 4265 "parser.tab.c"
    break;

  case 23: /* formula_role: lower_word  */
#line 501 "parser.y"
             { (yyval.data) = Tptp_mk_FormulaRole_lowerWord((yyvsp[0].data)); }
#line 4271 "parser.tab.c"
    break;

  case 24: /* formula_role: lower_word "-" general_term  */
#line 502 "parser.y"
                                { (yyval.data) = Tptp_mk_FormulaRole_lowerWordGeneralTerm((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4277 "parser.tab.c"
    break;

  case 25: /* thf_formula: thf_logic_formula  */
#line 506 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfFormula_thfLogicFormula((yyvsp[0].data)); }
#line 4283 "parser.tab.c"
    break;

  case 26: /* thf_formula: thf_atom_typing  */
#line 507 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfFormula_thfAtomTyping((yyvsp[0].data)); }
#line 4289 "parser.tab.c"
    break;

  case 27: /* thf_formula: thf_subtype  */
#line 508 "parser.y"
                { (yyval.data) = Tptp_mk_ThfFormula_thfSubtype((yyvsp[0].data)); }
#line 4295 "parser.tab.c"
    break;

  case 28: /* thf_logic_formula: thf_unitary_formula  */
#line 512 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfLogicFormula_thfUnitaryFormula((yyvsp[0].data)); }
#line 4301 "parser.tab.c"
    break;

  case 29: /* thf_logic_formula: thf_unary_formula  */
#line 513 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfLogicFormula_thfUnaryFormula((yyvsp[0].data)); }
#line 4307 "parser.tab.c"
    break;

  case 30: /* thf_logic_formula: thf_binary_formula  */
#line 514 "parser.y"
                       { (yyval.data) = Tptp_mk_ThfLogicFormula_thfBinaryFormula((yyvsp[0].data)); }
#line 4313 "parser.tab.c"
    break;

  case 31: /* thf_logic_formula: thf_defined_infix  */
#line 515 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfLogicFormula_thfDefinedInfix((yyvsp[0].data)); }
#line 4319 "parser.tab.c"
    break;

  case 32: /* thf_logic_formula: thf_definition  */
#line 516 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfLogicFormula_thfDefinition((yyvsp[0].data)); }
#line 4325 "parser.tab.c"
    break;

  case 33: /* thf_logic_formula: thf_sequent  */
#line 517 "parser.y"
                { (yyval.data) = Tptp_mk_ThfLogicFormula_thfSequent((yyvsp[0].data)); }
#line 4331 "parser.tab.c"
    break;

  case 34: /* thf_binary_formula: thf_binary_nonassoc  */
#line 521 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfBinaryFormula_thfBinaryNonassoc((yyvsp[0].data)); }
#line 4337 "parser.tab.c"
    break;

  case 35: /* thf_binary_formula: thf_binary_assoc  */
#line 522 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfBinaryFormula_thfBinaryAssoc((yyvsp[0].data)); }
#line 4343 "parser.tab.c"
    break;

  case 36: /* thf_binary_formula: thf_binary_type  */
#line 523 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfBinaryFormula_thfBinaryType((yyvsp[0].data)); }
#line 4349 "parser.tab.c"
    break;

  case 37: /* thf_binary_nonassoc: thf_unit_formula nonassoc_connective thf_unit_formula  */
#line 527 "parser.y"
                                                        { (yyval.data) = Tptp_mk_ThfBinaryNonassoc_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4355 "parser.tab.c"
    break;

  case 38: /* thf_binary_assoc: thf_or_formula  */
#line 531 "parser.y"
                 { (yyval.data) = Tptp_mk_ThfBinaryAssoc_thfOrFormula((yyvsp[0].data)); }
#line 4361 "parser.tab.c"
    break;

  case 39: /* thf_binary_assoc: thf_and_formula  */
#line 532 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfBinaryAssoc_thfAndFormula((yyvsp[0].data)); }
#line 4367 "parser.tab.c"
    break;

  case 40: /* thf_binary_assoc: thf_apply_formula  */
#line 533 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfBinaryAssoc_thfApplyFormula((yyvsp[0].data)); }
#line 4373 "parser.tab.c"
    break;

  case 41: /* thf_or_formula: thf_unit_formula "|" thf_unit_formula  */
#line 537 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfOrFormula_thfUnitFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4379 "parser.tab.c"
    break;

  case 42: /* thf_or_formula: thf_or_formula "|" thf_unit_formula  */
#line 538 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfOrFormula_thfOrFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4385 "parser.tab.c"
    break;

  case 43: /* thf_and_formula: thf_unit_formula "&" thf_unit_formula  */
#line 542 "parser.y"
                                        { (yyval.data) = Tptp_mk_ThfAndFormula_thfUnitFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4391 "parser.tab.c"
    break;

  case 44: /* thf_and_formula: thf_and_formula "&" thf_unit_formula  */
#line 543 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfAndFormula_thfAndFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4397 "parser.tab.c"
    break;

  case 45: /* thf_apply_formula: infix_equality "@" thf_unit_formula  */
#line 549 "parser.y"
                                      {
    lean_object *head = Tptp_mk_ThfUnitFormula_thfUnitaryFormula(
      Tptp_mk_ThfUnitaryFormula_thfAtomicFormula(
        Tptp_mk_ThfAtomicFormula_thfDefinedAtomic(
          Tptp_mk_ThfDefinedAtomic_thfConnTerm(
            Tptp_mk_ThfConnTerm_infixEquality((yyvsp[-2].data))))));
    (yyval.data) = Tptp_mk_ThfApplyFormula_thfUnitFormulaThfUnitFormula(head, (yyvsp[0].data));
  }
#line 4410 "parser.tab.c"
    break;

  case 46: /* thf_apply_formula: thf_unit_formula "@" thf_unit_formula  */
#line 557 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfApplyFormula_thfUnitFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4416 "parser.tab.c"
    break;

  case 47: /* thf_apply_formula: thf_apply_formula "@" thf_unit_formula  */
#line 558 "parser.y"
                                           { (yyval.data) = Tptp_mk_ThfApplyFormula_thfApplyFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4422 "parser.tab.c"
    break;

  case 48: /* thf_unit_formula: thf_unitary_formula  */
#line 562 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfUnitFormula_thfUnitaryFormula((yyvsp[0].data)); }
#line 4428 "parser.tab.c"
    break;

  case 49: /* thf_unit_formula: thf_unary_formula  */
#line 563 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfUnitFormula_thfUnaryFormula((yyvsp[0].data)); }
#line 4434 "parser.tab.c"
    break;

  case 50: /* thf_unit_formula: thf_defined_infix  */
#line 564 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfUnitFormula_thfDefinedInfix((yyvsp[0].data)); }
#line 4440 "parser.tab.c"
    break;

  case 51: /* thf_preunit_formula: thf_defined_infix  */
#line 569 "parser.y"
                    {
    (yyval.data) = Tptp_mk_ThfPreunitFormula_thfUnitaryFormula(
      Tptp_mk_ThfUnitaryFormula_thfLogicFormula(
        Tptp_mk_ThfLogicFormula_thfDefinedInfix((yyvsp[0].data))));
  }
#line 4450 "parser.tab.c"
    break;

  case 52: /* thf_preunit_formula: thf_infix_unary  */
#line 574 "parser.y"
                    {
    (yyval.data) = Tptp_mk_ThfPreunitFormula_thfUnitaryFormula(
      Tptp_mk_ThfUnitaryFormula_thfLogicFormula(
        Tptp_mk_ThfLogicFormula_thfUnaryFormula(
          Tptp_mk_ThfUnaryFormula_thfInfixUnary((yyvsp[0].data)))));
  }
#line 4461 "parser.tab.c"
    break;

  case 53: /* thf_preunit_formula: thf_unitary_formula  */
#line 580 "parser.y"
                        { (yyval.data) = Tptp_mk_ThfPreunitFormula_thfUnitaryFormula((yyvsp[0].data)); }
#line 4467 "parser.tab.c"
    break;

  case 54: /* thf_preunit_formula: thf_prefix_unary  */
#line 581 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfPreunitFormula_thfPrefixUnary((yyvsp[0].data)); }
#line 4473 "parser.tab.c"
    break;

  case 55: /* thf_unitary_formula: thf_quantified_formula  */
#line 585 "parser.y"
                         { (yyval.data) = Tptp_mk_ThfUnitaryFormula_thfQuantifiedFormula((yyvsp[0].data)); }
#line 4479 "parser.tab.c"
    break;

  case 56: /* thf_unitary_formula: thf_atomic_formula  */
#line 586 "parser.y"
                       { (yyval.data) = Tptp_mk_ThfUnitaryFormula_thfAtomicFormula((yyvsp[0].data)); }
#line 4485 "parser.tab.c"
    break;

  case 57: /* thf_unitary_formula: variable  */
#line 587 "parser.y"
             { (yyval.data) = Tptp_mk_ThfUnitaryFormula_variable((yyvsp[0].data)); }
#line 4491 "parser.tab.c"
    break;

  case 58: /* thf_unitary_formula: "(" thf_logic_formula ")"  */
#line 588 "parser.y"
                              { (yyval.data) = Tptp_mk_ThfUnitaryFormula_thfLogicFormula((yyvsp[-1].data)); }
#line 4497 "parser.tab.c"
    break;

  case 59: /* thf_quantified_formula: thf_quantification thf_unit_formula  */
#line 592 "parser.y"
                                      { (yyval.data) = Tptp_mk_ThfQuantifiedFormula_mk((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4503 "parser.tab.c"
    break;

  case 60: /* thf_quantification: thf_quantifier "[" thf_variable_list "]" ":"  */
#line 596 "parser.y"
                                               { (yyval.data) = Tptp_mk_ThfQuantification_mk((yyvsp[-4].data), (yyvsp[-2].data)); }
#line 4509 "parser.tab.c"
    break;

  case 61: /* thf_variable_list: thf_typed_variable  */
#line 600 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfVariableList_thfTypedVariable((yyvsp[0].data)); }
#line 4515 "parser.tab.c"
    break;

  case 62: /* thf_variable_list: thf_typed_variable "," thf_variable_list  */
#line 601 "parser.y"
                                             { (yyval.data) = Tptp_mk_ThfVariableList_thfTypedVariableThfVariableList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4521 "parser.tab.c"
    break;

  case 63: /* thf_typed_variable: variable ":" thf_top_level_type  */
#line 605 "parser.y"
                                  { (yyval.data) = Tptp_mk_ThfTypedVariable_mk((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4527 "parser.tab.c"
    break;

  case 64: /* thf_unary_formula: thf_prefix_unary  */
#line 609 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfUnaryFormula_thfPrefixUnary((yyvsp[0].data)); }
#line 4533 "parser.tab.c"
    break;

  case 65: /* thf_unary_formula: thf_infix_unary  */
#line 610 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfUnaryFormula_thfInfixUnary((yyvsp[0].data)); }
#line 4539 "parser.tab.c"
    break;

  case 66: /* thf_prefix_unary: thf_unary_connective thf_preunit_formula  */
#line 614 "parser.y"
                                           { (yyval.data) = Tptp_mk_ThfPrefixUnary_mk((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4545 "parser.tab.c"
    break;

  case 67: /* thf_infix_unary: thf_unitary_term infix_inequality thf_unitary_term  */
#line 618 "parser.y"
                                                     { (yyval.data) = Tptp_mk_ThfInfixUnary_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4551 "parser.tab.c"
    break;

  case 68: /* thf_atomic_formula: thf_plain_atomic  */
#line 622 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfAtomicFormula_thfPlainAtomic((yyvsp[0].data)); }
#line 4557 "parser.tab.c"
    break;

  case 69: /* thf_atomic_formula: thf_defined_atomic  */
#line 623 "parser.y"
                       { (yyval.data) = Tptp_mk_ThfAtomicFormula_thfDefinedAtomic((yyvsp[0].data)); }
#line 4563 "parser.tab.c"
    break;

  case 70: /* thf_atomic_formula: thf_system_atomic  */
#line 624 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfAtomicFormula_thfSystemAtomic((yyvsp[0].data)); }
#line 4569 "parser.tab.c"
    break;

  case 71: /* thf_atomic_formula: thf_fof_function  */
#line 625 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfAtomicFormula_thfFofFunction((yyvsp[0].data)); }
#line 4575 "parser.tab.c"
    break;

  case 72: /* thf_plain_atomic: constant  */
#line 629 "parser.y"
           { (yyval.data) = Tptp_mk_ThfPlainAtomic_constant((yyvsp[0].data)); }
#line 4581 "parser.tab.c"
    break;

  case 73: /* thf_plain_atomic: thf_tuple  */
#line 630 "parser.y"
              { (yyval.data) = Tptp_mk_ThfPlainAtomic_thfTuple((yyvsp[0].data)); }
#line 4587 "parser.tab.c"
    break;

  case 74: /* thf_defined_atomic: defined_constant  */
#line 634 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfDefinedAtomic_definedConstant((yyvsp[0].data)); }
#line 4593 "parser.tab.c"
    break;

  case 75: /* thf_defined_atomic: thf_defined_term  */
#line 635 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfDefinedAtomic_thfDefinedTerm((yyvsp[0].data)); }
#line 4599 "parser.tab.c"
    break;

  case 76: /* thf_defined_atomic: "(" thf_conn_term ")"  */
#line 636 "parser.y"
                          { (yyval.data) = Tptp_mk_ThfDefinedAtomic_thfConnTerm((yyvsp[-1].data)); }
#line 4605 "parser.tab.c"
    break;

  case 77: /* thf_defined_atomic: nhf_long_connective  */
#line 637 "parser.y"
                        { (yyval.data) = Tptp_mk_ThfDefinedAtomic_nhfLongConnective((yyvsp[0].data)); }
#line 4611 "parser.tab.c"
    break;

  case 78: /* thf_defined_atomic: thf_let  */
#line 638 "parser.y"
            { (yyval.data) = Tptp_mk_ThfDefinedAtomic_thfLet((yyvsp[0].data)); }
#line 4617 "parser.tab.c"
    break;

  case 79: /* thf_defined_term: defined_term  */
#line 642 "parser.y"
               { (yyval.data) = Tptp_mk_ThfDefinedTerm_definedTerm((yyvsp[0].data)); }
#line 4623 "parser.tab.c"
    break;

  case 80: /* thf_defined_term: th1_defined_term  */
#line 643 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfDefinedTerm_th1DefinedTerm((yyvsp[0].data)); }
#line 4629 "parser.tab.c"
    break;

  case 81: /* thf_defined_infix: thf_unitary_term defined_infix_pred thf_unitary_term  */
#line 647 "parser.y"
                                                       { (yyval.data) = Tptp_mk_ThfDefinedInfix_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4635 "parser.tab.c"
    break;

  case 82: /* thf_system_atomic: system_constant  */
#line 651 "parser.y"
                  { (yyval.data) = Tptp_mk_ThfSystemAtomic_mk((yyvsp[0].data)); }
#line 4641 "parser.tab.c"
    break;

  case 83: /* thf_let: "$let(" thf_let_types "," thf_let_defns "," thf_logic_formula ")"  */
#line 655 "parser.y"
                                                                    { (yyval.data) = Tptp_mk_ThfLet_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 4647 "parser.tab.c"
    break;

  case 84: /* thf_let_types: thf_atom_typing  */
#line 659 "parser.y"
                  { (yyval.data) = Tptp_mk_ThfLetTypes_thfAtomTyping((yyvsp[0].data)); }
#line 4653 "parser.tab.c"
    break;

  case 85: /* thf_let_types: "[" thf_atom_typing_list "]"  */
#line 660 "parser.y"
                                 { (yyval.data) = Tptp_mk_ThfLetTypes_thfAtomTypingList((yyvsp[-1].data)); }
#line 4659 "parser.tab.c"
    break;

  case 86: /* thf_atom_typing_list: thf_atom_typing  */
#line 664 "parser.y"
                  { (yyval.data) = Tptp_mk_ThfAtomTypingList_thfAtomTyping((yyvsp[0].data)); }
#line 4665 "parser.tab.c"
    break;

  case 87: /* thf_atom_typing_list: thf_atom_typing "," thf_atom_typing_list  */
#line 665 "parser.y"
                                             { (yyval.data) = Tptp_mk_ThfAtomTypingList_thfAtomTypingThfAtomTypingList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4671 "parser.tab.c"
    break;

  case 88: /* thf_let_defns: thf_let_defn  */
#line 669 "parser.y"
               { (yyval.data) = Tptp_mk_ThfLetDefns_thfLetDefn((yyvsp[0].data)); }
#line 4677 "parser.tab.c"
    break;

  case 89: /* thf_let_defns: "[" thf_let_defn_list "]"  */
#line 670 "parser.y"
                              { (yyval.data) = Tptp_mk_ThfLetDefns_thfLetDefnList((yyvsp[-1].data)); }
#line 4683 "parser.tab.c"
    break;

  case 90: /* thf_let_defn: thf_logic_formula assignment thf_logic_formula  */
#line 674 "parser.y"
                                                 { (yyval.data) = Tptp_mk_ThfLetDefn_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4689 "parser.tab.c"
    break;

  case 91: /* thf_let_defn_list: thf_let_defn  */
#line 678 "parser.y"
               { (yyval.data) = Tptp_mk_ThfLetDefnList_thfLetDefn((yyvsp[0].data)); }
#line 4695 "parser.tab.c"
    break;

  case 92: /* thf_let_defn_list: thf_let_defn "," thf_let_defn_list  */
#line 679 "parser.y"
                                       { (yyval.data) = Tptp_mk_ThfLetDefnList_thfLetDefnThfLetDefnList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4701 "parser.tab.c"
    break;

  case 93: /* thf_unitary_term: thf_atomic_formula  */
#line 683 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfUnitaryTerm_thfAtomicFormula((yyvsp[0].data)); }
#line 4707 "parser.tab.c"
    break;

  case 94: /* thf_unitary_term: variable  */
#line 684 "parser.y"
             { (yyval.data) = Tptp_mk_ThfUnitaryTerm_variable((yyvsp[0].data)); }
#line 4713 "parser.tab.c"
    break;

  case 95: /* thf_unitary_term: "(" thf_logic_formula ")"  */
#line 685 "parser.y"
                              { (yyval.data) = Tptp_mk_ThfUnitaryTerm_thfLogicFormula((yyvsp[-1].data)); }
#line 4719 "parser.tab.c"
    break;

  case 96: /* thf_conn_term: nonassoc_connective  */
#line 689 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfConnTerm_nonassocConnective((yyvsp[0].data)); }
#line 4725 "parser.tab.c"
    break;

  case 97: /* thf_conn_term: assoc_connective  */
#line 690 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfConnTerm_assocConnective((yyvsp[0].data)); }
#line 4731 "parser.tab.c"
    break;

  case 98: /* thf_conn_term: infix_equality  */
#line 691 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfConnTerm_infixEquality((yyvsp[0].data)); }
#line 4737 "parser.tab.c"
    break;

  case 99: /* thf_conn_term: infix_inequality  */
#line 692 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfConnTerm_infixInequality((yyvsp[0].data)); }
#line 4743 "parser.tab.c"
    break;

  case 100: /* thf_conn_term: thf_unary_connective  */
#line 693 "parser.y"
                         { (yyval.data) = Tptp_mk_ThfConnTerm_thfUnaryConnective((yyvsp[0].data)); }
#line 4749 "parser.tab.c"
    break;

  case 101: /* thf_tuple: "[]"  */
#line 697 "parser.y"
       { (yyval.data) = Tptp_mk_ThfTuple_empty; }
#line 4755 "parser.tab.c"
    break;

  case 102: /* thf_tuple: "[" thf_formula_list "]"  */
#line 698 "parser.y"
                             { (yyval.data) = Tptp_mk_ThfTuple_thfFormulaList((yyvsp[-1].data)); }
#line 4761 "parser.tab.c"
    break;

  case 103: /* thf_fof_function: functor "(" thf_arguments ")"  */
#line 702 "parser.y"
                                { (yyval.data) = Tptp_mk_ThfFofFunction_functorThfArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 4767 "parser.tab.c"
    break;

  case 104: /* thf_fof_function: defined_functor "(" thf_arguments ")"  */
#line 703 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfFofFunction_definedFunctorThfArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 4773 "parser.tab.c"
    break;

  case 105: /* thf_fof_function: system_functor "(" thf_arguments ")"  */
#line 704 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfFofFunction_systemFunctorThfArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 4779 "parser.tab.c"
    break;

  case 106: /* thf_arguments: thf_formula_list  */
#line 708 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfArguments_mk((yyvsp[0].data)); }
#line 4785 "parser.tab.c"
    break;

  case 107: /* thf_formula_list: thf_logic_formula comma_thf_logic_formula_list  */
#line 712 "parser.y"
                                                 { (yyval.data) = Tptp_mk_ThfFormulaList_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 4791 "parser.tab.c"
    break;

  case 108: /* comma_thf_logic_formula_list: %empty  */
#line 716 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 4797 "parser.tab.c"
    break;

  case 109: /* comma_thf_logic_formula_list: comma_thf_logic_formula_list comma_thf_logic_formula  */
#line 717 "parser.y"
                                                         { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4803 "parser.tab.c"
    break;

  case 110: /* comma_thf_logic_formula: "," thf_logic_formula  */
#line 721 "parser.y"
                        { (yyval.data) = Tptp_mk_CommaThfLogicFormula_mk((yyvsp[0].data)); }
#line 4809 "parser.tab.c"
    break;

  case 111: /* thf_atom_typing: untyped_atom ":" thf_top_level_type  */
#line 725 "parser.y"
                                      { (yyval.data) = Tptp_mk_ThfAtomTyping_untypedAtomThfTopLevelType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4815 "parser.tab.c"
    break;

  case 112: /* thf_atom_typing: "(" thf_atom_typing ")"  */
#line 726 "parser.y"
                            { (yyval.data) = Tptp_mk_ThfAtomTyping_thfAtomTyping((yyvsp[-1].data)); }
#line 4821 "parser.tab.c"
    break;

  case 113: /* thf_top_level_type: thf_unitary_type  */
#line 730 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfTopLevelType_thfUnitaryType((yyvsp[0].data)); }
#line 4827 "parser.tab.c"
    break;

  case 114: /* thf_top_level_type: thf_mapping_type  */
#line 731 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfTopLevelType_thfMappingType((yyvsp[0].data)); }
#line 4833 "parser.tab.c"
    break;

  case 115: /* thf_top_level_type: thf_apply_type  */
#line 732 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfTopLevelType_thfApplyType((yyvsp[0].data)); }
#line 4839 "parser.tab.c"
    break;

  case 116: /* thf_unitary_type: thf_unitary_formula  */
#line 736 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfUnitaryType_mk((yyvsp[0].data)); }
#line 4845 "parser.tab.c"
    break;

  case 117: /* thf_apply_type: thf_apply_formula  */
#line 740 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfApplyType_mk((yyvsp[0].data)); }
#line 4851 "parser.tab.c"
    break;

  case 118: /* thf_binary_type: thf_mapping_type  */
#line 744 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfBinaryType_thfMappingType((yyvsp[0].data)); }
#line 4857 "parser.tab.c"
    break;

  case 119: /* thf_binary_type: thf_xprod_type  */
#line 745 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfBinaryType_thfXprodType((yyvsp[0].data)); }
#line 4863 "parser.tab.c"
    break;

  case 120: /* thf_binary_type: thf_union_type  */
#line 746 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfBinaryType_thfUnionType((yyvsp[0].data)); }
#line 4869 "parser.tab.c"
    break;

  case 121: /* thf_mapping_type: thf_unitary_type ">" thf_unitary_type  */
#line 750 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfMappingType_thfUnitaryTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4875 "parser.tab.c"
    break;

  case 122: /* thf_mapping_type: thf_unitary_type ">" thf_mapping_type  */
#line 751 "parser.y"
                                            { (yyval.data) = Tptp_mk_ThfMappingType_thfUnitaryTypeThfMappingType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4881 "parser.tab.c"
    break;

  case 123: /* thf_xprod_type: thf_unitary_type "*" thf_unitary_type  */
#line 755 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfXprodType_thfUnitaryTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4887 "parser.tab.c"
    break;

  case 124: /* thf_xprod_type: thf_xprod_type "*" thf_unitary_type  */
#line 756 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfXprodType_thfXprodTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4893 "parser.tab.c"
    break;

  case 125: /* thf_union_type: thf_unitary_type "+" thf_unitary_type  */
#line 760 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfUnionType_thfUnitaryTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4899 "parser.tab.c"
    break;

  case 126: /* thf_union_type: thf_union_type "+" thf_unitary_type  */
#line 761 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfUnionType_thfUnionTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4905 "parser.tab.c"
    break;

  case 127: /* thf_subtype: untyped_atom subtype_sign atom  */
#line 765 "parser.y"
                                 { (yyval.data) = Tptp_mk_ThfSubtype_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4911 "parser.tab.c"
    break;

  case 128: /* thf_definition: thf_atomic_formula identical thf_logic_formula  */
#line 769 "parser.y"
                                                 { (yyval.data) = Tptp_mk_ThfDefinition_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4917 "parser.tab.c"
    break;

  case 129: /* thf_sequent: thf_tuple gentzen_arrow thf_tuple  */
#line 773 "parser.y"
                                    { (yyval.data) = Tptp_mk_ThfSequent_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4923 "parser.tab.c"
    break;

  case 130: /* tff_formula: tff_logic_formula  */
#line 777 "parser.y"
                    { (yyval.data) = Tptp_mk_TffFormula_tffLogicFormula((yyvsp[0].data)); }
#line 4929 "parser.tab.c"
    break;

  case 131: /* tff_formula: tff_atom_typing  */
#line 778 "parser.y"
                    { (yyval.data) = Tptp_mk_TffFormula_tffAtomTyping((yyvsp[0].data)); }
#line 4935 "parser.tab.c"
    break;

  case 132: /* tff_formula: tff_subtype  */
#line 779 "parser.y"
                { (yyval.data) = Tptp_mk_TffFormula_tffSubtype((yyvsp[0].data)); }
#line 4941 "parser.tab.c"
    break;

  case 133: /* tff_logic_formula: tff_unitary_formula  */
#line 783 "parser.y"
                      { (yyval.data) = Tptp_mk_TffLogicFormula_tffUnitaryFormula((yyvsp[0].data)); }
#line 4947 "parser.tab.c"
    break;

  case 134: /* tff_logic_formula: tff_unary_formula  */
#line 784 "parser.y"
                      { (yyval.data) = Tptp_mk_TffLogicFormula_tffUnaryFormula((yyvsp[0].data)); }
#line 4953 "parser.tab.c"
    break;

  case 135: /* tff_logic_formula: tff_binary_formula  */
#line 785 "parser.y"
                       { (yyval.data) = Tptp_mk_TffLogicFormula_tffBinaryFormula((yyvsp[0].data)); }
#line 4959 "parser.tab.c"
    break;

  case 136: /* tff_logic_formula: tff_defined_infix  */
#line 786 "parser.y"
                      { (yyval.data) = Tptp_mk_TffLogicFormula_tffDefinedInfix((yyvsp[0].data)); }
#line 4965 "parser.tab.c"
    break;

  case 137: /* tff_logic_formula: txf_definition  */
#line 787 "parser.y"
                   { (yyval.data) = Tptp_mk_TffLogicFormula_txfDefinition((yyvsp[0].data)); }
#line 4971 "parser.tab.c"
    break;

  case 138: /* tff_logic_formula: txf_sequent  */
#line 788 "parser.y"
                { (yyval.data) = Tptp_mk_TffLogicFormula_txfSequent((yyvsp[0].data)); }
#line 4977 "parser.tab.c"
    break;

  case 139: /* tff_binary_formula: tff_binary_nonassoc  */
#line 792 "parser.y"
                      { (yyval.data) = Tptp_mk_TffBinaryFormula_tffBinaryNonassoc((yyvsp[0].data)); }
#line 4983 "parser.tab.c"
    break;

  case 140: /* tff_binary_formula: tff_binary_assoc  */
#line 793 "parser.y"
                     { (yyval.data) = Tptp_mk_TffBinaryFormula_tffBinaryAssoc((yyvsp[0].data)); }
#line 4989 "parser.tab.c"
    break;

  case 141: /* tff_binary_nonassoc: tff_unit_formula nonassoc_connective tff_unit_formula  */
#line 797 "parser.y"
                                                        { (yyval.data) = Tptp_mk_TffBinaryNonassoc_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4995 "parser.tab.c"
    break;

  case 142: /* tff_binary_assoc: tff_or_formula  */
#line 801 "parser.y"
                 { (yyval.data) = Tptp_mk_TffBinaryAssoc_tffOrFormula((yyvsp[0].data)); }
#line 5001 "parser.tab.c"
    break;

  case 143: /* tff_binary_assoc: tff_and_formula  */
#line 802 "parser.y"
                    { (yyval.data) = Tptp_mk_TffBinaryAssoc_tffAndFormula((yyvsp[0].data)); }
#line 5007 "parser.tab.c"
    break;

  case 144: /* tff_or_formula: tff_unit_formula "|" tff_unit_formula  */
#line 806 "parser.y"
                                          { (yyval.data) = Tptp_mk_TffOrFormula_tffUnitFormulaTffUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5013 "parser.tab.c"
    break;

  case 145: /* tff_or_formula: tff_or_formula "|" tff_unit_formula  */
#line 807 "parser.y"
                                          { (yyval.data) = Tptp_mk_TffOrFormula_tffOrFormulaTffUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5019 "parser.tab.c"
    break;

  case 146: /* tff_and_formula: tff_unit_formula "&" tff_unit_formula  */
#line 811 "parser.y"
                                        { (yyval.data) = Tptp_mk_TffAndFormula_tffUnitFormulaTffUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5025 "parser.tab.c"
    break;

  case 147: /* tff_and_formula: tff_and_formula "&" tff_unit_formula  */
#line 812 "parser.y"
                                         { (yyval.data) = Tptp_mk_TffAndFormula_tffAndFormulaTffUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5031 "parser.tab.c"
    break;

  case 148: /* tff_unit_formula: tff_unitary_formula  */
#line 816 "parser.y"
                      { (yyval.data) = Tptp_mk_TffUnitFormula_tffUnitaryFormula((yyvsp[0].data)); }
#line 5037 "parser.tab.c"
    break;

  case 149: /* tff_unit_formula: tff_unary_formula  */
#line 817 "parser.y"
                      { (yyval.data) = Tptp_mk_TffUnitFormula_tffUnaryFormula((yyvsp[0].data)); }
#line 5043 "parser.tab.c"
    break;

  case 150: /* tff_unit_formula: tff_defined_infix  */
#line 818 "parser.y"
                      { (yyval.data) = Tptp_mk_TffUnitFormula_tffDefinedInfix((yyvsp[0].data)); }
#line 5049 "parser.tab.c"
    break;

  case 151: /* tff_preunit_formula: tff_defined_infix  */
#line 823 "parser.y"
                    {
    (yyval.data) = Tptp_mk_TffPreunitFormula_tffUnitaryFormula(
      Tptp_mk_TffUnitaryFormula_tffLogicFormula(
        Tptp_mk_TffLogicFormula_tffDefinedInfix((yyvsp[0].data))));
  }
#line 5059 "parser.tab.c"
    break;

  case 152: /* tff_preunit_formula: tff_infix_unary  */
#line 828 "parser.y"
                    {
    (yyval.data) = Tptp_mk_TffPreunitFormula_tffUnitaryFormula(
      Tptp_mk_TffUnitaryFormula_tffLogicFormula(
        Tptp_mk_TffLogicFormula_tffUnaryFormula(
          Tptp_mk_TffUnaryFormula_tffInfixUnary((yyvsp[0].data)))));
  }
#line 5070 "parser.tab.c"
    break;

  case 153: /* tff_preunit_formula: tff_unitary_formula  */
#line 834 "parser.y"
                        { (yyval.data) = Tptp_mk_TffPreunitFormula_tffUnitaryFormula((yyvsp[0].data)); }
#line 5076 "parser.tab.c"
    break;

  case 154: /* tff_preunit_formula: tff_prefix_unary  */
#line 835 "parser.y"
                     { (yyval.data) = Tptp_mk_TffPreunitFormula_tffPrefixUnary((yyvsp[0].data)); }
#line 5082 "parser.tab.c"
    break;

  case 155: /* tff_unitary_formula: tff_quantified_formula  */
#line 839 "parser.y"
                         { (yyval.data) = Tptp_mk_TffUnitaryFormula_tffQuantifiedFormula((yyvsp[0].data)); }
#line 5088 "parser.tab.c"
    break;

  case 156: /* tff_unitary_formula: tff_atomic_formula  */
#line 840 "parser.y"
                       { (yyval.data) = Tptp_mk_TffUnitaryFormula_tffAtomicFormula((yyvsp[0].data)); }
#line 5094 "parser.tab.c"
    break;

  case 157: /* tff_unitary_formula: txf_unitary_formula  */
#line 841 "parser.y"
                        { (yyval.data) = Tptp_mk_TffUnitaryFormula_txfUnitaryFormula((yyvsp[0].data)); }
#line 5100 "parser.tab.c"
    break;

  case 158: /* tff_unitary_formula: "(" tff_logic_formula ")"  */
#line 842 "parser.y"
                              { (yyval.data) = Tptp_mk_TffUnitaryFormula_tffLogicFormula((yyvsp[-1].data)); }
#line 5106 "parser.tab.c"
    break;

  case 159: /* txf_unitary_formula: variable  */
#line 846 "parser.y"
           { (yyval.data) = Tptp_mk_TxfUnitaryFormula_mk((yyvsp[0].data)); }
#line 5112 "parser.tab.c"
    break;

  case 160: /* tff_quantified_formula: tff_quantifier "[" tff_variable_list "]" ":" tff_unit_formula  */
#line 850 "parser.y"
                                                                { (yyval.data) = Tptp_mk_TffQuantifiedFormula_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[0].data)); }
#line 5118 "parser.tab.c"
    break;

  case 161: /* tff_variable_list: tff_variable  */
#line 854 "parser.y"
               { (yyval.data) = Tptp_mk_TffVariableList_tffVariable((yyvsp[0].data)); }
#line 5124 "parser.tab.c"
    break;

  case 162: /* tff_variable_list: tff_variable "," tff_variable_list  */
#line 855 "parser.y"
                                       { (yyval.data) = Tptp_mk_TffVariableList_tffVariableTffVariableList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5130 "parser.tab.c"
    break;

  case 163: /* tff_variable: tff_typed_variable  */
#line 859 "parser.y"
                     { (yyval.data) = Tptp_mk_TffVariable_tffTypedVariable((yyvsp[0].data)); }
#line 5136 "parser.tab.c"
    break;

  case 164: /* tff_variable: variable  */
#line 860 "parser.y"
             { (yyval.data) = Tptp_mk_TffVariable_variable((yyvsp[0].data)); }
#line 5142 "parser.tab.c"
    break;

  case 165: /* tff_typed_variable: variable ":" tff_atomic_type  */
#line 864 "parser.y"
                               { (yyval.data) = Tptp_mk_TffTypedVariable_mk((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5148 "parser.tab.c"
    break;

  case 166: /* tff_unary_formula: tff_prefix_unary  */
#line 868 "parser.y"
                   { (yyval.data) = Tptp_mk_TffUnaryFormula_tffPrefixUnary((yyvsp[0].data)); }
#line 5154 "parser.tab.c"
    break;

  case 167: /* tff_unary_formula: tff_infix_unary  */
#line 869 "parser.y"
                    { (yyval.data) = Tptp_mk_TffUnaryFormula_tffInfixUnary((yyvsp[0].data)); }
#line 5160 "parser.tab.c"
    break;

  case 168: /* tff_prefix_unary: tff_unary_connective tff_preunit_formula  */
#line 873 "parser.y"
                                           { (yyval.data) = Tptp_mk_TffPrefixUnary_mk((yyvsp[-1].data), (yyvsp[0].data)); }
#line 5166 "parser.tab.c"
    break;

  case 169: /* tff_infix_unary: tff_unitary_term infix_inequality tff_unitary_term  */
#line 877 "parser.y"
                                                     { (yyval.data) = Tptp_mk_TffInfixUnary_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5172 "parser.tab.c"
    break;

  case 170: /* tff_atomic_formula: tff_plain_atomic  */
#line 881 "parser.y"
                   { (yyval.data) = Tptp_mk_TffAtomicFormula_tffPlainAtomic((yyvsp[0].data)); }
#line 5178 "parser.tab.c"
    break;

  case 171: /* tff_atomic_formula: tff_defined_atomic  */
#line 882 "parser.y"
                       { (yyval.data) = Tptp_mk_TffAtomicFormula_tffDefinedAtomic((yyvsp[0].data)); }
#line 5184 "parser.tab.c"
    break;

  case 172: /* tff_atomic_formula: tff_system_atomic  */
#line 883 "parser.y"
                      { (yyval.data) = Tptp_mk_TffAtomicFormula_tffSystemAtomic((yyvsp[0].data)); }
#line 5190 "parser.tab.c"
    break;

  case 173: /* tff_plain_atomic: constant  */
#line 887 "parser.y"
           { (yyval.data) = Tptp_mk_TffPlainAtomic_constant((yyvsp[0].data)); }
#line 5196 "parser.tab.c"
    break;

  case 174: /* tff_plain_atomic: functor "(" tff_arguments ")"  */
#line 888 "parser.y"
                                  { (yyval.data) = Tptp_mk_TffPlainAtomic_functorTffArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5202 "parser.tab.c"
    break;

  case 175: /* tff_defined_atomic: tff_defined_plain  */
#line 892 "parser.y"
                    { (yyval.data) = Tptp_mk_TffDefinedAtomic_mk((yyvsp[0].data)); }
#line 5208 "parser.tab.c"
    break;

  case 176: /* tff_defined_plain: defined_constant  */
#line 896 "parser.y"
                   { (yyval.data) = Tptp_mk_TffDefinedPlain_definedConstant((yyvsp[0].data)); }
#line 5214 "parser.tab.c"
    break;

  case 177: /* tff_defined_plain: defined_functor "(" tff_arguments ")"  */
#line 897 "parser.y"
                                          { (yyval.data) = Tptp_mk_TffDefinedPlain_definedFunctorTffArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5220 "parser.tab.c"
    break;

  case 178: /* tff_defined_plain: nxf_atom  */
#line 898 "parser.y"
             { (yyval.data) = Tptp_mk_TffDefinedPlain_nxfAtom((yyvsp[0].data)); }
#line 5226 "parser.tab.c"
    break;

  case 179: /* tff_defined_plain: txf_let  */
#line 899 "parser.y"
            { (yyval.data) = Tptp_mk_TffDefinedPlain_txfLet((yyvsp[0].data)); }
#line 5232 "parser.tab.c"
    break;

  case 180: /* tff_defined_infix: tff_unitary_term defined_infix_pred tff_unitary_term  */
#line 903 "parser.y"
                                                       { (yyval.data) = Tptp_mk_TffDefinedInfix_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5238 "parser.tab.c"
    break;

  case 181: /* tff_system_atomic: system_constant  */
#line 907 "parser.y"
                  { (yyval.data) = Tptp_mk_TffSystemAtomic_systemConstant((yyvsp[0].data)); }
#line 5244 "parser.tab.c"
    break;

  case 182: /* tff_system_atomic: system_functor "(" tff_arguments ")"  */
#line 908 "parser.y"
                                         { (yyval.data) = Tptp_mk_TffSystemAtomic_systemFunctorTffArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5250 "parser.tab.c"
    break;

  case 183: /* txf_let: "$let(" txf_let_types "," txf_let_defns "," tff_term ")"  */
#line 912 "parser.y"
                                                           { (yyval.data) = Tptp_mk_TxfLet_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5256 "parser.tab.c"
    break;

  case 184: /* txf_let_types: tff_atom_typing  */
#line 916 "parser.y"
                  { (yyval.data) = Tptp_mk_TxfLetTypes_tffAtomTyping((yyvsp[0].data)); }
#line 5262 "parser.tab.c"
    break;

  case 185: /* txf_let_types: "[" tff_atom_typing_list "]"  */
#line 917 "parser.y"
                                 { (yyval.data) = Tptp_mk_TxfLetTypes_tffAtomTypingList((yyvsp[-1].data)); }
#line 5268 "parser.tab.c"
    break;

  case 186: /* tff_atom_typing_list: tff_atom_typing  */
#line 921 "parser.y"
                  { (yyval.data) = Tptp_mk_TffAtomTypingList_tffAtomTyping((yyvsp[0].data)); }
#line 5274 "parser.tab.c"
    break;

  case 187: /* tff_atom_typing_list: tff_atom_typing "," tff_atom_typing_list  */
#line 922 "parser.y"
                                             { (yyval.data) = Tptp_mk_TffAtomTypingList_tffAtomTypingTffAtomTypingList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5280 "parser.tab.c"
    break;

  case 188: /* txf_let_defns: txf_let_defn  */
#line 926 "parser.y"
               { (yyval.data) = Tptp_mk_TxfLetDefns_txfLetDefn((yyvsp[0].data)); }
#line 5286 "parser.tab.c"
    break;

  case 189: /* txf_let_defns: "[" txf_let_defn_list "]"  */
#line 927 "parser.y"
                              { (yyval.data) = Tptp_mk_TxfLetDefns_txfLetDefnList((yyvsp[-1].data)); }
#line 5292 "parser.tab.c"
    break;

  case 190: /* txf_let_defn: txf_let_LHS assignment tff_term  */
#line 931 "parser.y"
                                  { (yyval.data) = Tptp_mk_TxfLetDefn_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5298 "parser.tab.c"
    break;

  case 191: /* txf_let_LHS: tff_plain_atomic  */
#line 935 "parser.y"
                   { (yyval.data) = Tptp_mk_TxfLetLHS_tffPlainAtomic((yyvsp[0].data)); }
#line 5304 "parser.tab.c"
    break;

  case 192: /* txf_let_LHS: txf_tuple  */
#line 936 "parser.y"
              { (yyval.data) = Tptp_mk_TxfLetLHS_txfTuple((yyvsp[0].data)); }
#line 5310 "parser.tab.c"
    break;

  case 193: /* txf_let_defn_list: txf_let_defn  */
#line 940 "parser.y"
               { (yyval.data) = Tptp_mk_TxfLetDefnList_txfLetDefn((yyvsp[0].data)); }
#line 5316 "parser.tab.c"
    break;

  case 194: /* txf_let_defn_list: txf_let_defn "," txf_let_defn_list  */
#line 941 "parser.y"
                                       { (yyval.data) = Tptp_mk_TxfLetDefnList_txfLetDefnTxfLetDefnList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5322 "parser.tab.c"
    break;

  case 195: /* nxf_atom: nxf_long_connective "@" "(" tff_arguments ")"  */
#line 945 "parser.y"
                                                { (yyval.data) = Tptp_mk_NxfAtom_mk((yyvsp[-4].data), (yyvsp[-1].data)); }
#line 5328 "parser.tab.c"
    break;

  case 196: /* tff_term: tff_logic_formula  */
#line 949 "parser.y"
                    { (yyval.data) = Tptp_mk_TffTerm_tffLogicFormula((yyvsp[0].data)); }
#line 5334 "parser.tab.c"
    break;

  case 197: /* tff_term: defined_term  */
#line 950 "parser.y"
                 { (yyval.data) = Tptp_mk_TffTerm_definedTerm((yyvsp[0].data)); }
#line 5340 "parser.tab.c"
    break;

  case 198: /* tff_term: txf_tuple  */
#line 951 "parser.y"
              { (yyval.data) = Tptp_mk_TffTerm_txfTuple((yyvsp[0].data)); }
#line 5346 "parser.tab.c"
    break;

  case 199: /* tff_unitary_term: tff_atomic_formula  */
#line 955 "parser.y"
                     { (yyval.data) = Tptp_mk_TffUnitaryTerm_tffAtomicFormula((yyvsp[0].data)); }
#line 5352 "parser.tab.c"
    break;

  case 200: /* tff_unitary_term: defined_term  */
#line 956 "parser.y"
                 { (yyval.data) = Tptp_mk_TffUnitaryTerm_definedTerm((yyvsp[0].data)); }
#line 5358 "parser.tab.c"
    break;

  case 201: /* tff_unitary_term: txf_tuple  */
#line 957 "parser.y"
              { (yyval.data) = Tptp_mk_TffUnitaryTerm_txfTuple((yyvsp[0].data)); }
#line 5364 "parser.tab.c"
    break;

  case 202: /* tff_unitary_term: variable  */
#line 958 "parser.y"
             { (yyval.data) = Tptp_mk_TffUnitaryTerm_variable((yyvsp[0].data)); }
#line 5370 "parser.tab.c"
    break;

  case 203: /* tff_unitary_term: "(" tff_logic_formula ")"  */
#line 959 "parser.y"
                              { (yyval.data) = Tptp_mk_TffUnitaryTerm_tffLogicFormula((yyvsp[-1].data)); }
#line 5376 "parser.tab.c"
    break;

  case 204: /* txf_tuple: "[]"  */
#line 963 "parser.y"
       { (yyval.data) = Tptp_mk_TxfTuple_empty; }
#line 5382 "parser.tab.c"
    break;

  case 205: /* txf_tuple: "[" tff_arguments "]"  */
#line 964 "parser.y"
                          { (yyval.data) = Tptp_mk_TxfTuple_tffArguments((yyvsp[-1].data)); }
#line 5388 "parser.tab.c"
    break;

  case 206: /* tff_arguments: tff_term comma_tff_term_list  */
#line 968 "parser.y"
                               { (yyval.data) = Tptp_mk_TffArguments_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 5394 "parser.tab.c"
    break;

  case 207: /* comma_tff_term_list: %empty  */
#line 972 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 5400 "parser.tab.c"
    break;

  case 208: /* comma_tff_term_list: comma_tff_term_list comma_tff_term  */
#line 973 "parser.y"
                                       { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 5406 "parser.tab.c"
    break;

  case 209: /* comma_tff_term: "," tff_term  */
#line 977 "parser.y"
               { (yyval.data) = Tptp_mk_CommaTffTerm_mk((yyvsp[0].data)); }
#line 5412 "parser.tab.c"
    break;

  case 210: /* tff_atom_typing: untyped_atom ":" tff_top_level_type  */
#line 981 "parser.y"
                                      { (yyval.data) = Tptp_mk_TffAtomTyping_untypedAtomTffTopLevelType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5418 "parser.tab.c"
    break;

  case 211: /* tff_atom_typing: "(" tff_atom_typing ")"  */
#line 982 "parser.y"
                            { (yyval.data) = Tptp_mk_TffAtomTyping_tffAtomTyping((yyvsp[-1].data)); }
#line 5424 "parser.tab.c"
    break;

  case 212: /* tff_top_level_type: tff_atomic_type  */
#line 986 "parser.y"
                  { (yyval.data) = Tptp_mk_TffTopLevelType_tffAtomicType((yyvsp[0].data)); }
#line 5430 "parser.tab.c"
    break;

  case 213: /* tff_top_level_type: tff_non_atomic_type  */
#line 987 "parser.y"
                        { (yyval.data) = Tptp_mk_TffTopLevelType_tffNonAtomicType((yyvsp[0].data)); }
#line 5436 "parser.tab.c"
    break;

  case 214: /* tff_non_atomic_type: tff_mapping_type  */
#line 991 "parser.y"
                   { (yyval.data) = Tptp_mk_TffNonAtomicType_tffMappingType((yyvsp[0].data)); }
#line 5442 "parser.tab.c"
    break;

  case 215: /* tff_non_atomic_type: tf1_quantified_type  */
#line 992 "parser.y"
                        { (yyval.data) = Tptp_mk_TffNonAtomicType_tf1QuantifiedType((yyvsp[0].data)); }
#line 5448 "parser.tab.c"
    break;

  case 216: /* tff_non_atomic_type: "(" tff_non_atomic_type ")"  */
#line 993 "parser.y"
                                { (yyval.data) = Tptp_mk_TffNonAtomicType_tffNonAtomicType((yyvsp[-1].data)); }
#line 5454 "parser.tab.c"
    break;

  case 217: /* tf1_quantified_type: type_quantifier "[" tff_variable_list "]" ":" tff_monotype  */
#line 997 "parser.y"
                                                             { (yyval.data) = Tptp_mk_Tf1QuantifiedType_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[0].data)); }
#line 5460 "parser.tab.c"
    break;

  case 218: /* tff_monotype: tff_atomic_type  */
#line 1001 "parser.y"
                  { (yyval.data) = Tptp_mk_TffMonotype_tffAtomicType((yyvsp[0].data)); }
#line 5466 "parser.tab.c"
    break;

  case 219: /* tff_monotype: "(" tff_mapping_type ")"  */
#line 1002 "parser.y"
                             { (yyval.data) = Tptp_mk_TffMonotype_tffMappingType((yyvsp[-1].data)); }
#line 5472 "parser.tab.c"
    break;

  case 220: /* tff_monotype: tf1_quantified_type  */
#line 1003 "parser.y"
                        { (yyval.data) = Tptp_mk_TffMonotype_tf1QuantifiedType((yyvsp[0].data)); }
#line 5478 "parser.tab.c"
    break;

  case 221: /* tff_unitary_type: tff_atomic_type  */
#line 1007 "parser.y"
                  { (yyval.data) = Tptp_mk_TffUnitaryType_tffAtomicType((yyvsp[0].data)); }
#line 5484 "parser.tab.c"
    break;

  case 222: /* tff_unitary_type: "(" tff_xprod_type ")"  */
#line 1008 "parser.y"
                           { (yyval.data) = Tptp_mk_TffUnitaryType_tffXprodType((yyvsp[-1].data)); }
#line 5490 "parser.tab.c"
    break;

  case 223: /* tff_atomic_type: type_constant  */
#line 1012 "parser.y"
                { (yyval.data) = Tptp_mk_TffAtomicType_typeConstant((yyvsp[0].data)); }
#line 5496 "parser.tab.c"
    break;

  case 224: /* tff_atomic_type: defined_type  */
#line 1013 "parser.y"
                 { (yyval.data) = Tptp_mk_TffAtomicType_definedType((yyvsp[0].data)); }
#line 5502 "parser.tab.c"
    break;

  case 225: /* tff_atomic_type: variable  */
#line 1014 "parser.y"
             { (yyval.data) = Tptp_mk_TffAtomicType_variable((yyvsp[0].data)); }
#line 5508 "parser.tab.c"
    break;

  case 226: /* tff_atomic_type: type_functor "(" tff_type_arguments ")"  */
#line 1015 "parser.y"
                                            { (yyval.data) = Tptp_mk_TffAtomicType_typeFunctorTffTypeArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5514 "parser.tab.c"
    break;

  case 227: /* tff_atomic_type: "(" tff_atomic_type ")"  */
#line 1016 "parser.y"
                            { (yyval.data) = Tptp_mk_TffAtomicType_tffAtomicType((yyvsp[-1].data)); }
#line 5520 "parser.tab.c"
    break;

  case 228: /* tff_atomic_type: txf_tuple_type  */
#line 1017 "parser.y"
                   { (yyval.data) = Tptp_mk_TffAtomicType_txfTupleType((yyvsp[0].data)); }
#line 5526 "parser.tab.c"
    break;

  case 229: /* tff_type_arguments: tff_atomic_type  */
#line 1021 "parser.y"
                  { (yyval.data) = Tptp_mk_TffTypeArguments_tffAtomicType((yyvsp[0].data)); }
#line 5532 "parser.tab.c"
    break;

  case 230: /* tff_type_arguments: tff_atomic_type "," tff_type_arguments  */
#line 1022 "parser.y"
                                           { (yyval.data) = Tptp_mk_TffTypeArguments_tffAtomicTypeTffTypeArguments((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5538 "parser.tab.c"
    break;

  case 231: /* tff_mapping_type: tff_unitary_type ">" tff_atomic_type  */
#line 1026 "parser.y"
                                         { (yyval.data) = Tptp_mk_TffMappingType_mk((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5544 "parser.tab.c"
    break;

  case 232: /* tff_xprod_type: tff_unitary_type "*" tff_atomic_type  */
#line 1030 "parser.y"
                                        { (yyval.data) = Tptp_mk_TffXprodType_tffUnitaryTypeTffAtomicType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5550 "parser.tab.c"
    break;

  case 233: /* tff_xprod_type: tff_xprod_type "*" tff_atomic_type  */
#line 1031 "parser.y"
                                        { (yyval.data) = Tptp_mk_TffXprodType_tffXprodTypeTffAtomicType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5556 "parser.tab.c"
    break;

  case 234: /* txf_tuple_type: "[" tff_type_list "]"  */
#line 1035 "parser.y"
                        { (yyval.data) = Tptp_mk_TxfTupleType_mk((yyvsp[-1].data)); }
#line 5562 "parser.tab.c"
    break;

  case 235: /* tff_type_list: tff_top_level_type  */
#line 1039 "parser.y"
                     { (yyval.data) = Tptp_mk_TffTypeList_tffTopLevelType((yyvsp[0].data)); }
#line 5568 "parser.tab.c"
    break;

  case 236: /* tff_type_list: tff_top_level_type "," tff_type_list  */
#line 1040 "parser.y"
                                         { (yyval.data) = Tptp_mk_TffTypeList_tffTopLevelTypeTffTypeList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5574 "parser.tab.c"
    break;

  case 237: /* tff_subtype: untyped_atom subtype_sign atom  */
#line 1044 "parser.y"
                                 { (yyval.data) = Tptp_mk_TffSubtype_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5580 "parser.tab.c"
    break;

  case 238: /* txf_definition: tff_atomic_formula identical tff_term  */
#line 1048 "parser.y"
                                        { (yyval.data) = Tptp_mk_TxfDefinition_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5586 "parser.tab.c"
    break;

  case 239: /* txf_sequent: txf_tuple gentzen_arrow txf_tuple  */
#line 1052 "parser.y"
                                    { (yyval.data) = Tptp_mk_TxfSequent_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5592 "parser.tab.c"
    break;

  case 240: /* nhf_long_connective: "{" ntf_connective_name "}"  */
#line 1056 "parser.y"
                              { (yyval.data) = Tptp_mk_NhfLongConnective_ntfConnectiveName((yyvsp[-1].data)); }
#line 5598 "parser.tab.c"
    break;

  case 241: /* nhf_long_connective: "{" ntf_connective_name "(" nhf_parameter_list ")}"  */
#line 1057 "parser.y"
                                                        { (yyval.data) = Tptp_mk_NhfLongConnective_ntfConnectiveNameNhfParameterList((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5604 "parser.tab.c"
    break;

  case 242: /* nhf_parameter_list: nhf_parameter  */
#line 1061 "parser.y"
                { (yyval.data) = Tptp_mk_NhfParameterList_nhfParameter((yyvsp[0].data)); }
#line 5610 "parser.tab.c"
    break;

  case 243: /* nhf_parameter_list: nhf_parameter "," nhf_parameter_list  */
#line 1062 "parser.y"
                                         { (yyval.data) = Tptp_mk_NhfParameterList_nhfParameterNhfParameterList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5616 "parser.tab.c"
    break;

  case 244: /* nhf_parameter: ntf_index  */
#line 1066 "parser.y"
            { (yyval.data) = Tptp_mk_NhfParameter_ntfIndex((yyvsp[0].data)); }
#line 5622 "parser.tab.c"
    break;

  case 245: /* nhf_parameter: nhf_key_pair  */
#line 1067 "parser.y"
                 { (yyval.data) = Tptp_mk_NhfParameter_nhfKeyPair((yyvsp[0].data)); }
#line 5628 "parser.tab.c"
    break;

  case 246: /* nhf_key_pair: thf_definition  */
#line 1071 "parser.y"
                 { (yyval.data) = Tptp_mk_NhfKeyPair_mk((yyvsp[0].data)); }
#line 5634 "parser.tab.c"
    break;

  case 247: /* nxf_long_connective: "{" ntf_connective_name "}"  */
#line 1075 "parser.y"
                              { (yyval.data) = Tptp_mk_NxfLongConnective_ntfConnectiveName((yyvsp[-1].data)); }
#line 5640 "parser.tab.c"
    break;

  case 248: /* nxf_long_connective: "{" ntf_connective_name "(" nxf_parameter_list ")}"  */
#line 1076 "parser.y"
                                                        { (yyval.data) = Tptp_mk_NxfLongConnective_ntfConnectiveNameNxfParameterList((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5646 "parser.tab.c"
    break;

  case 249: /* nxf_parameter_list: nxf_parameter  */
#line 1080 "parser.y"
                { (yyval.data) = Tptp_mk_NxfParameterList_nxfParameter((yyvsp[0].data)); }
#line 5652 "parser.tab.c"
    break;

  case 250: /* nxf_parameter_list: nxf_parameter "," nxf_parameter_list  */
#line 1081 "parser.y"
                                         { (yyval.data) = Tptp_mk_NxfParameterList_nxfParameterNxfParameterList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5658 "parser.tab.c"
    break;

  case 251: /* nxf_parameter: ntf_index  */
#line 1085 "parser.y"
            { (yyval.data) = Tptp_mk_NxfParameter_ntfIndex((yyvsp[0].data)); }
#line 5664 "parser.tab.c"
    break;

  case 252: /* nxf_parameter: nxf_key_pair  */
#line 1086 "parser.y"
                 { (yyval.data) = Tptp_mk_NxfParameter_nxfKeyPair((yyvsp[0].data)); }
#line 5670 "parser.tab.c"
    break;

  case 253: /* nxf_key_pair: txf_definition  */
#line 1090 "parser.y"
                 { (yyval.data) = Tptp_mk_NxfKeyPair_mk((yyvsp[0].data)); }
#line 5676 "parser.tab.c"
    break;

  case 254: /* ntf_connective_name: def_or_sys_constant  */
#line 1094 "parser.y"
                      { (yyval.data) = Tptp_mk_NtfConnectiveName_mk((yyvsp[0].data)); }
#line 5682 "parser.tab.c"
    break;

  case 255: /* ntf_index: "#" tff_unitary_term  */
#line 1098 "parser.y"
                        { (yyval.data) = Tptp_mk_NtfIndex_mk((yyvsp[0].data)); }
#line 5688 "parser.tab.c"
    break;

  case 256: /* ntf_short_connective: "[.]"  */
#line 1102 "parser.y"
        { (yyval.data) = Tptp_mk_NtfShortConnective_bracket; }
#line 5694 "parser.tab.c"
    break;

  case 257: /* ntf_short_connective: "<" "." ">"  */
#line 1103 "parser.y"
                        { (yyval.data) = Tptp_mk_NtfShortConnective_angle; }
#line 5700 "parser.tab.c"
    break;

  case 258: /* ntf_short_connective: "{.}"  */
#line 1104 "parser.y"
          { (yyval.data) = Tptp_mk_NtfShortConnective_brace; }
#line 5706 "parser.tab.c"
    break;

  case 259: /* ntf_short_connective: "(.)"  */
#line 1105 "parser.y"
          { (yyval.data) = Tptp_mk_NtfShortConnective_parens; }
#line 5712 "parser.tab.c"
    break;

  case 260: /* tcf_formula: tcf_logic_formula  */
#line 1109 "parser.y"
                    { (yyval.data) = Tptp_mk_TcfFormula_tcfLogicFormula((yyvsp[0].data)); }
#line 5718 "parser.tab.c"
    break;

  case 261: /* tcf_formula: tff_atom_typing  */
#line 1110 "parser.y"
                    { (yyval.data) = Tptp_mk_TcfFormula_tffAtomTyping((yyvsp[0].data)); }
#line 5724 "parser.tab.c"
    break;

  case 262: /* tcf_logic_formula: tcf_quantified_formula  */
#line 1114 "parser.y"
                         { (yyval.data) = Tptp_mk_TcfLogicFormula_tcfQuantifiedFormula((yyvsp[0].data)); }
#line 5730 "parser.tab.c"
    break;

  case 263: /* tcf_logic_formula: cnf_formula  */
#line 1115 "parser.y"
                { (yyval.data) = Tptp_mk_TcfLogicFormula_cnfFormula((yyvsp[0].data)); }
#line 5736 "parser.tab.c"
    break;

  case 264: /* tcf_quantified_formula: "!" "[" tff_variable_list "]" ":" tcf_logic_formula  */
#line 1119 "parser.y"
                                                      { (yyval.data) = Tptp_mk_TcfQuantifiedFormula_mk((yyvsp[-3].data), (yyvsp[0].data)); }
#line 5742 "parser.tab.c"
    break;

  case 265: /* fof_formula: fof_logic_formula  */
#line 1123 "parser.y"
                    { (yyval.data) = Tptp_mk_FofFormula_fofLogicFormula((yyvsp[0].data)); }
#line 5748 "parser.tab.c"
    break;

  case 266: /* fof_formula: fof_sequent  */
#line 1124 "parser.y"
                { (yyval.data) = Tptp_mk_FofFormula_fofSequent((yyvsp[0].data)); }
#line 5754 "parser.tab.c"
    break;

  case 267: /* fof_logic_formula: fof_binary_formula  */
#line 1128 "parser.y"
                     { (yyval.data) = Tptp_mk_FofLogicFormula_fofBinaryFormula((yyvsp[0].data)); }
#line 5760 "parser.tab.c"
    break;

  case 268: /* fof_logic_formula: fof_unary_formula  */
#line 1129 "parser.y"
                      { (yyval.data) = Tptp_mk_FofLogicFormula_fofUnaryFormula((yyvsp[0].data)); }
#line 5766 "parser.tab.c"
    break;

  case 269: /* fof_logic_formula: fof_unitary_formula  */
#line 1130 "parser.y"
                        { (yyval.data) = Tptp_mk_FofLogicFormula_fofUnitaryFormula((yyvsp[0].data)); }
#line 5772 "parser.tab.c"
    break;

  case 270: /* fof_binary_formula: fof_binary_nonassoc  */
#line 1134 "parser.y"
                      { (yyval.data) = Tptp_mk_FofBinaryFormula_fofBinaryNonassoc((yyvsp[0].data)); }
#line 5778 "parser.tab.c"
    break;

  case 271: /* fof_binary_formula: fof_binary_assoc  */
#line 1135 "parser.y"
                     { (yyval.data) = Tptp_mk_FofBinaryFormula_fofBinaryAssoc((yyvsp[0].data)); }
#line 5784 "parser.tab.c"
    break;

  case 272: /* fof_binary_nonassoc: fof_unit_formula nonassoc_connective fof_unit_formula  */
#line 1139 "parser.y"
                                                        { (yyval.data) = Tptp_mk_FofBinaryNonassoc_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5790 "parser.tab.c"
    break;

  case 273: /* fof_binary_assoc: fof_or_formula  */
#line 1143 "parser.y"
                 { (yyval.data) = Tptp_mk_FofBinaryAssoc_fofOrFormula((yyvsp[0].data)); }
#line 5796 "parser.tab.c"
    break;

  case 274: /* fof_binary_assoc: fof_and_formula  */
#line 1144 "parser.y"
                    { (yyval.data) = Tptp_mk_FofBinaryAssoc_fofAndFormula((yyvsp[0].data)); }
#line 5802 "parser.tab.c"
    break;

  case 275: /* fof_or_formula: fof_unit_formula "|" fof_unit_formula  */
#line 1148 "parser.y"
                                          { (yyval.data) = Tptp_mk_FofOrFormula_fofUnitFormulaFofUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5808 "parser.tab.c"
    break;

  case 276: /* fof_or_formula: fof_or_formula "|" fof_unit_formula  */
#line 1149 "parser.y"
                                          { (yyval.data) = Tptp_mk_FofOrFormula_fofOrFormulaFofUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5814 "parser.tab.c"
    break;

  case 277: /* fof_and_formula: fof_unit_formula "&" fof_unit_formula  */
#line 1153 "parser.y"
                                        { (yyval.data) = Tptp_mk_FofAndFormula_fofUnitFormulaFofUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5820 "parser.tab.c"
    break;

  case 278: /* fof_and_formula: fof_and_formula "&" fof_unit_formula  */
#line 1154 "parser.y"
                                         { (yyval.data) = Tptp_mk_FofAndFormula_fofAndFormulaFofUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5826 "parser.tab.c"
    break;

  case 279: /* fof_unary_formula: unary_connective fof_unit_formula  */
#line 1158 "parser.y"
                                    { (yyval.data) = Tptp_mk_FofUnaryFormula_unaryConnectiveFofUnitFormula((yyvsp[-1].data), (yyvsp[0].data)); }
#line 5832 "parser.tab.c"
    break;

  case 280: /* fof_unary_formula: fof_infix_unary  */
#line 1159 "parser.y"
                    { (yyval.data) = Tptp_mk_FofUnaryFormula_fofInfixUnary((yyvsp[0].data)); }
#line 5838 "parser.tab.c"
    break;

  case 281: /* fof_infix_unary: fof_term infix_inequality fof_term  */
#line 1163 "parser.y"
                                     { (yyval.data) = Tptp_mk_FofInfixUnary_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5844 "parser.tab.c"
    break;

  case 282: /* fof_unit_formula: fof_unitary_formula  */
#line 1167 "parser.y"
                      { (yyval.data) = Tptp_mk_FofUnitFormula_fofUnitaryFormula((yyvsp[0].data)); }
#line 5850 "parser.tab.c"
    break;

  case 283: /* fof_unit_formula: fof_unary_formula  */
#line 1168 "parser.y"
                      { (yyval.data) = Tptp_mk_FofUnitFormula_fofUnaryFormula((yyvsp[0].data)); }
#line 5856 "parser.tab.c"
    break;

  case 284: /* fof_unitary_formula: fof_quantified_formula  */
#line 1172 "parser.y"
                         { (yyval.data) = Tptp_mk_FofUnitaryFormula_fofQuantifiedFormula((yyvsp[0].data)); }
#line 5862 "parser.tab.c"
    break;

  case 285: /* fof_unitary_formula: fof_atomic_formula  */
#line 1173 "parser.y"
                       { (yyval.data) = Tptp_mk_FofUnitaryFormula_fofAtomicFormula((yyvsp[0].data)); }
#line 5868 "parser.tab.c"
    break;

  case 286: /* fof_unitary_formula: "(" fof_logic_formula ")"  */
#line 1174 "parser.y"
                              { (yyval.data) = Tptp_mk_FofUnitaryFormula_fofLogicFormula((yyvsp[-1].data)); }
#line 5874 "parser.tab.c"
    break;

  case 287: /* fof_quantified_formula: fof_quantifier "[" fof_variable_list "]" ":" fof_unit_formula  */
#line 1178 "parser.y"
                                                                { (yyval.data) = Tptp_mk_FofQuantifiedFormula_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[0].data)); }
#line 5880 "parser.tab.c"
    break;

  case 288: /* fof_variable_list: variable  */
#line 1182 "parser.y"
           { (yyval.data) = Tptp_mk_FofVariableList_variable((yyvsp[0].data)); }
#line 5886 "parser.tab.c"
    break;

  case 289: /* fof_variable_list: variable "," fof_variable_list  */
#line 1183 "parser.y"
                                   { (yyval.data) = Tptp_mk_FofVariableList_variableFofVariableList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5892 "parser.tab.c"
    break;

  case 290: /* fof_atomic_formula: fof_plain_atomic_formula  */
#line 1187 "parser.y"
                           { (yyval.data) = Tptp_mk_FofAtomicFormula_fofPlainAtomicFormula((yyvsp[0].data)); }
#line 5898 "parser.tab.c"
    break;

  case 291: /* fof_atomic_formula: fof_defined_atomic_formula  */
#line 1188 "parser.y"
                               { (yyval.data) = Tptp_mk_FofAtomicFormula_fofDefinedAtomicFormula((yyvsp[0].data)); }
#line 5904 "parser.tab.c"
    break;

  case 292: /* fof_atomic_formula: fof_system_atomic_formula  */
#line 1189 "parser.y"
                              { (yyval.data) = Tptp_mk_FofAtomicFormula_fofSystemAtomicFormula((yyvsp[0].data)); }
#line 5910 "parser.tab.c"
    break;

  case 293: /* fof_plain_atomic_formula: fof_plain_term  */
#line 1193 "parser.y"
                 { (yyval.data) = Tptp_mk_FofPlainAtomicFormula_mk((yyvsp[0].data)); }
#line 5916 "parser.tab.c"
    break;

  case 294: /* fof_defined_atomic_formula: fof_defined_plain_formula  */
#line 1197 "parser.y"
                            { (yyval.data) = Tptp_mk_FofDefinedAtomicFormula_fofDefinedPlainFormula((yyvsp[0].data)); }
#line 5922 "parser.tab.c"
    break;

  case 295: /* fof_defined_atomic_formula: fof_defined_infix_formula  */
#line 1198 "parser.y"
                              { (yyval.data) = Tptp_mk_FofDefinedAtomicFormula_fofDefinedInfixFormula((yyvsp[0].data)); }
#line 5928 "parser.tab.c"
    break;

  case 296: /* fof_defined_plain_formula: fof_defined_plain_term  */
#line 1202 "parser.y"
                         { (yyval.data) = Tptp_mk_FofDefinedPlainFormula_mk((yyvsp[0].data)); }
#line 5934 "parser.tab.c"
    break;

  case 297: /* fof_defined_infix_formula: fof_term defined_infix_pred fof_term  */
#line 1206 "parser.y"
                                       { (yyval.data) = Tptp_mk_FofDefinedInfixFormula_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5940 "parser.tab.c"
    break;

  case 298: /* fof_system_atomic_formula: fof_system_term  */
#line 1210 "parser.y"
                  { (yyval.data) = Tptp_mk_FofSystemAtomicFormula_mk((yyvsp[0].data)); }
#line 5946 "parser.tab.c"
    break;

  case 299: /* fof_plain_term: constant  */
#line 1214 "parser.y"
           { (yyval.data) = Tptp_mk_FofPlainTerm_constant((yyvsp[0].data)); }
#line 5952 "parser.tab.c"
    break;

  case 300: /* fof_plain_term: functor "(" fof_arguments ")"  */
#line 1215 "parser.y"
                                  { (yyval.data) = Tptp_mk_FofPlainTerm_functorFofArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5958 "parser.tab.c"
    break;

  case 301: /* fof_defined_term: defined_term  */
#line 1219 "parser.y"
               { (yyval.data) = Tptp_mk_FofDefinedTerm_definedTerm((yyvsp[0].data)); }
#line 5964 "parser.tab.c"
    break;

  case 302: /* fof_defined_term: fof_defined_atomic_term  */
#line 1220 "parser.y"
                            { (yyval.data) = Tptp_mk_FofDefinedTerm_fofDefinedAtomicTerm((yyvsp[0].data)); }
#line 5970 "parser.tab.c"
    break;

  case 303: /* fof_defined_atomic_term: fof_defined_plain_term  */
#line 1224 "parser.y"
                         { (yyval.data) = Tptp_mk_FofDefinedAtomicTerm_mk((yyvsp[0].data)); }
#line 5976 "parser.tab.c"
    break;

  case 304: /* fof_defined_plain_term: defined_constant  */
#line 1228 "parser.y"
                   { (yyval.data) = Tptp_mk_FofDefinedPlainTerm_definedConstant((yyvsp[0].data)); }
#line 5982 "parser.tab.c"
    break;

  case 305: /* fof_defined_plain_term: defined_functor "(" fof_arguments ")"  */
#line 1229 "parser.y"
                                          { (yyval.data) = Tptp_mk_FofDefinedPlainTerm_definedFunctorFofArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5988 "parser.tab.c"
    break;

  case 306: /* fof_system_term: system_constant  */
#line 1233 "parser.y"
                  { (yyval.data) = Tptp_mk_FofSystemTerm_systemConstant((yyvsp[0].data)); }
#line 5994 "parser.tab.c"
    break;

  case 307: /* fof_system_term: system_functor "(" fof_arguments ")"  */
#line 1234 "parser.y"
                                         { (yyval.data) = Tptp_mk_FofSystemTerm_systemFunctorFofArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6000 "parser.tab.c"
    break;

  case 308: /* fof_arguments: fof_term  */
#line 1238 "parser.y"
           { (yyval.data) = Tptp_mk_FofArguments_fofTerm((yyvsp[0].data)); }
#line 6006 "parser.tab.c"
    break;

  case 309: /* fof_arguments: fof_term "," fof_arguments  */
#line 1239 "parser.y"
                               { (yyval.data) = Tptp_mk_FofArguments_fofTermFofArguments((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6012 "parser.tab.c"
    break;

  case 310: /* fof_term: fof_function_term  */
#line 1243 "parser.y"
                    { (yyval.data) = Tptp_mk_FofTerm_fofFunctionTerm((yyvsp[0].data)); }
#line 6018 "parser.tab.c"
    break;

  case 311: /* fof_term: variable  */
#line 1244 "parser.y"
             { (yyval.data) = Tptp_mk_FofTerm_variable((yyvsp[0].data)); }
#line 6024 "parser.tab.c"
    break;

  case 312: /* fof_function_term: fof_plain_term  */
#line 1248 "parser.y"
                 { (yyval.data) = Tptp_mk_FofFunctionTerm_fofPlainTerm((yyvsp[0].data)); }
#line 6030 "parser.tab.c"
    break;

  case 313: /* fof_function_term: fof_defined_term  */
#line 1249 "parser.y"
                     { (yyval.data) = Tptp_mk_FofFunctionTerm_fofDefinedTerm((yyvsp[0].data)); }
#line 6036 "parser.tab.c"
    break;

  case 314: /* fof_function_term: fof_system_term  */
#line 1250 "parser.y"
                    { (yyval.data) = Tptp_mk_FofFunctionTerm_fofSystemTerm((yyvsp[0].data)); }
#line 6042 "parser.tab.c"
    break;

  case 315: /* fof_sequent: fof_formula_tuple gentzen_arrow fof_formula_tuple  */
#line 1254 "parser.y"
                                                    { (yyval.data) = Tptp_mk_FofSequent_fofFormulaTupleGentzenArrowFofFormulaTuple((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 6048 "parser.tab.c"
    break;

  case 316: /* fof_sequent: "(" fof_sequent ")"  */
#line 1255 "parser.y"
                        { (yyval.data) = Tptp_mk_FofSequent_fofSequent((yyvsp[-1].data)); }
#line 6054 "parser.tab.c"
    break;

  case 317: /* fof_formula_tuple: "[]"  */
#line 1259 "parser.y"
       { (yyval.data) = Tptp_mk_FofFormulaTuple_empty; }
#line 6060 "parser.tab.c"
    break;

  case 318: /* fof_formula_tuple: "[" fof_formula_tuple_list "]"  */
#line 1260 "parser.y"
                                   { (yyval.data) = Tptp_mk_FofFormulaTuple_fofFormulaTupleList((yyvsp[-1].data)); }
#line 6066 "parser.tab.c"
    break;

  case 319: /* fof_formula_tuple_list: fof_logic_formula comma_fof_logic_formula_list  */
#line 1264 "parser.y"
                                                 { (yyval.data) = Tptp_mk_FofFormulaTupleList_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 6072 "parser.tab.c"
    break;

  case 320: /* comma_fof_logic_formula_list: %empty  */
#line 1268 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 6078 "parser.tab.c"
    break;

  case 321: /* comma_fof_logic_formula_list: comma_fof_logic_formula_list comma_fof_logic_formula  */
#line 1269 "parser.y"
                                                         { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 6084 "parser.tab.c"
    break;

  case 322: /* comma_fof_logic_formula: "," fof_logic_formula  */
#line 1273 "parser.y"
                        { (yyval.data) = Tptp_mk_CommaFofLogicFormula_mk((yyvsp[0].data)); }
#line 6090 "parser.tab.c"
    break;

  case 323: /* cnf_formula: cnf_disjunction  */
#line 1277 "parser.y"
                  { (yyval.data) = Tptp_mk_CnfFormula_cnfDisjunction((yyvsp[0].data)); }
#line 6096 "parser.tab.c"
    break;

  case 324: /* cnf_formula: "(" cnf_formula ")"  */
#line 1278 "parser.y"
                        { (yyval.data) = Tptp_mk_CnfFormula_cnfFormula((yyvsp[-1].data)); }
#line 6102 "parser.tab.c"
    break;

  case 325: /* cnf_disjunction: cnf_literal  */
#line 1282 "parser.y"
              { (yyval.data) = Tptp_mk_CnfDisjunction_cnfLiteral((yyvsp[0].data)); }
#line 6108 "parser.tab.c"
    break;

  case 326: /* cnf_disjunction: cnf_disjunction "|" cnf_literal  */
#line 1283 "parser.y"
                                      { (yyval.data) = Tptp_mk_CnfDisjunction_cnfDisjunctionCnfLiteral((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6114 "parser.tab.c"
    break;

  case 327: /* cnf_literal: fof_atomic_formula  */
#line 1287 "parser.y"
                     { (yyval.data) = Tptp_mk_CnfLiteral_fofAtomicFormula((yyvsp[0].data)); }
#line 6120 "parser.tab.c"
    break;

  case 328: /* cnf_literal: "~" fof_atomic_formula  */
#line 1288 "parser.y"
                           { (yyval.data) = Tptp_mk_CnfLiteral_fofAtomicFormulaNegated((yyvsp[0].data)); }
#line 6126 "parser.tab.c"
    break;

  case 329: /* cnf_literal: "~" "(" fof_atomic_formula ")"  */
#line 1289 "parser.y"
                                   { (yyval.data) = Tptp_mk_CnfLiteral_fofAtomicFormulaNegated((yyvsp[-1].data)); }
#line 6132 "parser.tab.c"
    break;

  case 330: /* cnf_literal: fof_infix_unary  */
#line 1290 "parser.y"
                    { (yyval.data) = Tptp_mk_CnfLiteral_fofInfixUnary((yyvsp[0].data)); }
#line 6138 "parser.tab.c"
    break;

  case 331: /* thf_quantifier: tff_quantifier  */
#line 1294 "parser.y"
                 { (yyval.data) = Tptp_mk_ThfQuantifier_tffQuantifier((yyvsp[0].data)); }
#line 6144 "parser.tab.c"
    break;

  case 332: /* thf_quantifier: th0_quantifier  */
#line 1295 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfQuantifier_th0Quantifier((yyvsp[0].data)); }
#line 6150 "parser.tab.c"
    break;

  case 333: /* thf_quantifier: type_quantifier  */
#line 1296 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfQuantifier_typeQuantifier((yyvsp[0].data)); }
#line 6156 "parser.tab.c"
    break;

  case 334: /* thf_unary_connective: unary_connective  */
#line 1300 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfUnaryConnective_unaryConnective((yyvsp[0].data)); }
#line 6162 "parser.tab.c"
    break;

  case 335: /* thf_unary_connective: ntf_short_connective  */
#line 1301 "parser.y"
                         { (yyval.data) = Tptp_mk_ThfUnaryConnective_ntfShortConnective((yyvsp[0].data)); }
#line 6168 "parser.tab.c"
    break;

  case 336: /* th0_quantifier: "^"  */
#line 1305 "parser.y"
      { (yyval.data) = Tptp_mk_Th0Quantifier_caret; }
#line 6174 "parser.tab.c"
    break;

  case 337: /* th0_quantifier: "@+"  */
#line 1306 "parser.y"
         { (yyval.data) = Tptp_mk_Th0Quantifier_atPlus; }
#line 6180 "parser.tab.c"
    break;

  case 338: /* th0_quantifier: "@-"  */
#line 1307 "parser.y"
         { (yyval.data) = Tptp_mk_Th0Quantifier_atMinus; }
#line 6186 "parser.tab.c"
    break;

  case 339: /* type_quantifier: "!>"  */
#line 1311 "parser.y"
       { (yyval.data) = Tptp_mk_TypeQuantifier_exclamationArrow; }
#line 6192 "parser.tab.c"
    break;

  case 340: /* type_quantifier: "?*"  */
#line 1312 "parser.y"
         { (yyval.data) = Tptp_mk_TypeQuantifier_questionStar; }
#line 6198 "parser.tab.c"
    break;

  case 341: /* subtype_sign: "<<"  */
#line 1316 "parser.y"
       { (yyval.data) = Tptp_mk_SubtypeSign_mk; }
#line 6204 "parser.tab.c"
    break;

  case 342: /* tff_unary_connective: unary_connective  */
#line 1320 "parser.y"
                   { (yyval.data) = Tptp_mk_TffUnaryConnective_unaryConnective((yyvsp[0].data)); }
#line 6210 "parser.tab.c"
    break;

  case 343: /* tff_unary_connective: ntf_short_connective  */
#line 1321 "parser.y"
                         { (yyval.data) = Tptp_mk_TffUnaryConnective_ntfShortConnective((yyvsp[0].data)); }
#line 6216 "parser.tab.c"
    break;

  case 344: /* tff_quantifier: fof_quantifier  */
#line 1325 "parser.y"
                 { (yyval.data) = Tptp_mk_TffQuantifier_fofQuantifier((yyvsp[0].data)); }
#line 6222 "parser.tab.c"
    break;

  case 345: /* tff_quantifier: "#"  */
#line 1326 "parser.y"
         { (yyval.data) = Tptp_mk_TffQuantifier_hash; }
#line 6228 "parser.tab.c"
    break;

  case 346: /* fof_quantifier: "!"  */
#line 1330 "parser.y"
      { (yyval.data) = Tptp_mk_FofQuantifier_exclamation; }
#line 6234 "parser.tab.c"
    break;

  case 347: /* fof_quantifier: "?"  */
#line 1331 "parser.y"
        { (yyval.data) = Tptp_mk_FofQuantifier_question; }
#line 6240 "parser.tab.c"
    break;

  case 348: /* nonassoc_connective: "<=>"  */
#line 1335 "parser.y"
        { (yyval.data) = Tptp_mk_NonassocConnective_iff; }
#line 6246 "parser.tab.c"
    break;

  case 349: /* nonassoc_connective: "=>"  */
#line 1336 "parser.y"
         { (yyval.data) = Tptp_mk_NonassocConnective_fi; }
#line 6252 "parser.tab.c"
    break;

  case 350: /* nonassoc_connective: "<="  */
#line 1337 "parser.y"
         { (yyval.data) = Tptp_mk_NonassocConnective_if; }
#line 6258 "parser.tab.c"
    break;

  case 351: /* nonassoc_connective: "<~>"  */
#line 1338 "parser.y"
          { (yyval.data) = Tptp_mk_NonassocConnective_xor; }
#line 6264 "parser.tab.c"
    break;

  case 352: /* nonassoc_connective: "~" "|"  */
#line 1339 "parser.y"
              { (yyval.data) = Tptp_mk_NonassocConnective_nor; }
#line 6270 "parser.tab.c"
    break;

  case 353: /* nonassoc_connective: "~&"  */
#line 1340 "parser.y"
         { (yyval.data) = Tptp_mk_NonassocConnective_nand; }
#line 6276 "parser.tab.c"
    break;

  case 354: /* assoc_connective: "|"  */
#line 1344 "parser.y"
        { (yyval.data) = Tptp_mk_AssocConnective_or; }
#line 6282 "parser.tab.c"
    break;

  case 355: /* assoc_connective: "&"  */
#line 1345 "parser.y"
        { (yyval.data) = Tptp_mk_AssocConnective_and; }
#line 6288 "parser.tab.c"
    break;

  case 356: /* unary_connective: "~"  */
#line 1349 "parser.y"
      { (yyval.data) = Tptp_mk_UnaryConnective_mk; }
#line 6294 "parser.tab.c"
    break;

  case 357: /* gentzen_arrow: "-->"  */
#line 1353 "parser.y"
        { (yyval.data) = Tptp_mk_GentzenArrow_mk; }
#line 6300 "parser.tab.c"
    break;

  case 358: /* assignment: ":="  */
#line 1357 "parser.y"
       { (yyval.data) = Tptp_mk_Assignment_mk; }
#line 6306 "parser.tab.c"
    break;

  case 359: /* identical: "=="  */
#line 1361 "parser.y"
       { (yyval.data) = Tptp_mk_Identical_mk; }
#line 6312 "parser.tab.c"
    break;

  case 360: /* type_constant: type_functor  */
#line 1365 "parser.y"
               { (yyval.data) = Tptp_mk_TypeConstant_mk((yyvsp[0].data)); }
#line 6318 "parser.tab.c"
    break;

  case 361: /* type_functor: atomic_word  */
#line 1369 "parser.y"
              { (yyval.data) = Tptp_mk_TypeFunctor_mk((yyvsp[0].data)); }
#line 6324 "parser.tab.c"
    break;

  case 362: /* defined_type: atomic_defined_word  */
#line 1373 "parser.y"
                      { (yyval.data) = Tptp_mk_DefinedType_mk((yyvsp[0].data)); }
#line 6330 "parser.tab.c"
    break;

  case 363: /* atom: untyped_atom  */
#line 1377 "parser.y"
               { (yyval.data) = Tptp_mk_Atom_untypedAtom((yyvsp[0].data)); }
#line 6336 "parser.tab.c"
    break;

  case 364: /* atom: defined_constant  */
#line 1378 "parser.y"
                     { (yyval.data) = Tptp_mk_Atom_definedConstant((yyvsp[0].data)); }
#line 6342 "parser.tab.c"
    break;

  case 365: /* untyped_atom: constant  */
#line 1382 "parser.y"
           { (yyval.data) = Tptp_mk_UntypedAtom_constant((yyvsp[0].data)); }
#line 6348 "parser.tab.c"
    break;

  case 366: /* untyped_atom: system_constant  */
#line 1383 "parser.y"
                    { (yyval.data) = Tptp_mk_UntypedAtom_systemConstant((yyvsp[0].data)); }
#line 6354 "parser.tab.c"
    break;

  case 367: /* defined_infix_pred: infix_equality  */
#line 1387 "parser.y"
                 { (yyval.data) = Tptp_mk_DefinedInfixPred_mk((yyvsp[0].data)); }
#line 6360 "parser.tab.c"
    break;

  case 368: /* infix_equality: "="  */
#line 1391 "parser.y"
      { (yyval.data) = Tptp_mk_InfixEquality_mk; }
#line 6366 "parser.tab.c"
    break;

  case 369: /* infix_inequality: "!="  */
#line 1395 "parser.y"
       { (yyval.data) = Tptp_mk_InfixInequality_mk; }
#line 6372 "parser.tab.c"
    break;

  case 370: /* constant: functor  */
#line 1399 "parser.y"
          { (yyval.data) = Tptp_mk_Constant_mk((yyvsp[0].data)); }
#line 6378 "parser.tab.c"
    break;

  case 371: /* functor: atomic_word  */
#line 1403 "parser.y"
              { (yyval.data) = Tptp_mk_Functor_mk((yyvsp[0].data)); }
#line 6384 "parser.tab.c"
    break;

  case 372: /* defined_constant: defined_functor  */
#line 1407 "parser.y"
                  { (yyval.data) = Tptp_mk_DefinedConstant_mk((yyvsp[0].data)); }
#line 6390 "parser.tab.c"
    break;

  case 373: /* defined_functor: atomic_defined_word  */
#line 1411 "parser.y"
                      { (yyval.data) = Tptp_mk_DefinedFunctor_mk((yyvsp[0].data)); }
#line 6396 "parser.tab.c"
    break;

  case 374: /* system_constant: system_functor  */
#line 1415 "parser.y"
                 { (yyval.data) = Tptp_mk_SystemConstant_mk((yyvsp[0].data)); }
#line 6402 "parser.tab.c"
    break;

  case 375: /* system_functor: atomic_system_word  */
#line 1419 "parser.y"
                     { (yyval.data) = Tptp_mk_SystemFunctor_mk((yyvsp[0].data)); }
#line 6408 "parser.tab.c"
    break;

  case 376: /* def_or_sys_constant: defined_constant  */
#line 1423 "parser.y"
                   { (yyval.data) = Tptp_mk_DefOrSysConstant_definedConstant((yyvsp[0].data)); }
#line 6414 "parser.tab.c"
    break;

  case 377: /* def_or_sys_constant: system_constant  */
#line 1424 "parser.y"
                    { (yyval.data) = Tptp_mk_DefOrSysConstant_systemConstant((yyvsp[0].data)); }
#line 6420 "parser.tab.c"
    break;

  case 378: /* th1_defined_term: "!!"  */
#line 1428 "parser.y"
       { (yyval.data) = Tptp_mk_Th1DefinedTerm_doubleExclamation; }
#line 6426 "parser.tab.c"
    break;

  case 379: /* th1_defined_term: "??"  */
#line 1429 "parser.y"
         { (yyval.data) = Tptp_mk_Th1DefinedTerm_doubleQuestion; }
#line 6432 "parser.tab.c"
    break;

  case 380: /* th1_defined_term: "@@+"  */
#line 1430 "parser.y"
          { (yyval.data) = Tptp_mk_Th1DefinedTerm_doubleAtPlus; }
#line 6438 "parser.tab.c"
    break;

  case 381: /* th1_defined_term: "@@-"  */
#line 1431 "parser.y"
          { (yyval.data) = Tptp_mk_Th1DefinedTerm_doubleAtMinus; }
#line 6444 "parser.tab.c"
    break;

  case 382: /* th1_defined_term: "@="  */
#line 1432 "parser.y"
         { (yyval.data) = Tptp_mk_Th1DefinedTerm_atEquals; }
#line 6450 "parser.tab.c"
    break;

  case 383: /* distinct_object: DISTINCT_OBJECT  */
#line 1436 "parser.y"
                  { (yyval.data) = Tptp_mk_DistinctObject_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6456 "parser.tab.c"
    break;

  case 384: /* defined_term: number  */
#line 1440 "parser.y"
         { (yyval.data) = Tptp_mk_DefinedTerm_number((yyvsp[0].data)); }
#line 6462 "parser.tab.c"
    break;

  case 385: /* defined_term: distinct_object  */
#line 1441 "parser.y"
                    { (yyval.data) = Tptp_mk_DefinedTerm_distinctObject((yyvsp[0].data)); }
#line 6468 "parser.tab.c"
    break;

  case 386: /* upper_word: UPPER_WORD  */
#line 1445 "parser.y"
             { (yyval.data) = Tptp_mk_UpperWord_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6474 "parser.tab.c"
    break;

  case 387: /* variable: upper_word  */
#line 1449 "parser.y"
             { (yyval.data) = Tptp_mk_Variable_mk((yyvsp[0].data)); }
#line 6480 "parser.tab.c"
    break;

  case 388: /* source: "unknown"  */
#line 1454 "parser.y"
            { (yyval.data) = Tptp_mk_Source_unknown; }
#line 6486 "parser.tab.c"
    break;

  case 389: /* source: dag_source  */
#line 1455 "parser.y"
               { (yyval.data) = Tptp_mk_Source_dagSource((yyvsp[0].data)); }
#line 6492 "parser.tab.c"
    break;

  case 390: /* source: internal_source  */
#line 1456 "parser.y"
                    { (yyval.data) = Tptp_mk_Source_internalSource((yyvsp[0].data)); }
#line 6498 "parser.tab.c"
    break;

  case 391: /* source: external_source  */
#line 1457 "parser.y"
                    { (yyval.data) = Tptp_mk_Source_externalSource((yyvsp[0].data)); }
#line 6504 "parser.tab.c"
    break;

  case 392: /* source: "[" sources "]"  */
#line 1458 "parser.y"
                    { (yyval.data) = Tptp_mk_Source_sources((yyvsp[-1].data)); }
#line 6510 "parser.tab.c"
    break;

  case 393: /* sources: source  */
#line 1462 "parser.y"
         { (yyval.data) = Tptp_mk_Sources_source((yyvsp[0].data)); }
#line 6516 "parser.tab.c"
    break;

  case 394: /* sources: source "," sources  */
#line 1463 "parser.y"
                       { (yyval.data) = Tptp_mk_Sources_sourceSources((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6522 "parser.tab.c"
    break;

  case 395: /* dag_source: name  */
#line 1467 "parser.y"
       { (yyval.data) = Tptp_mk_DagSource_name((yyvsp[0].data)); }
#line 6528 "parser.tab.c"
    break;

  case 396: /* dag_source: inference_record  */
#line 1468 "parser.y"
                     { (yyval.data) = Tptp_mk_DagSource_inferenceRecord((yyvsp[0].data)); }
#line 6534 "parser.tab.c"
    break;

  case 397: /* inference_record: "inference(" inference_rule "," useful_info "," parents ")"  */
#line 1472 "parser.y"
                                                              { (yyval.data) = Tptp_mk_InferenceRecord_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6540 "parser.tab.c"
    break;

  case 398: /* inference_rule: atomic_word  */
#line 1476 "parser.y"
              { (yyval.data) = Tptp_mk_InferenceRule_mk((yyvsp[0].data)); }
#line 6546 "parser.tab.c"
    break;

  case 399: /* internal_source: "introduced(" intro_type "," useful_info "," parents ")"  */
#line 1480 "parser.y"
                                                           { (yyval.data) = Tptp_mk_InternalSource_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6552 "parser.tab.c"
    break;

  case 400: /* intro_type: atomic_word  */
#line 1484 "parser.y"
              { (yyval.data) = Tptp_mk_IntroType_mk((yyvsp[0].data)); }
#line 6558 "parser.tab.c"
    break;

  case 401: /* external_source: file_source  */
#line 1488 "parser.y"
              { (yyval.data) = Tptp_mk_ExternalSource_fileSource((yyvsp[0].data)); }
#line 6564 "parser.tab.c"
    break;

  case 402: /* external_source: theory  */
#line 1489 "parser.y"
           { (yyval.data) = Tptp_mk_ExternalSource_theory((yyvsp[0].data)); }
#line 6570 "parser.tab.c"
    break;

  case 403: /* external_source: creator_source  */
#line 1490 "parser.y"
                   { (yyval.data) = Tptp_mk_ExternalSource_creatorSource((yyvsp[0].data)); }
#line 6576 "parser.tab.c"
    break;

  case 404: /* file_source: "file(" file_name file_info ")"  */
#line 1494 "parser.y"
                                  { (yyval.data) = Tptp_mk_FileSource_mk((yyvsp[-2].data), (yyvsp[-1].data)); }
#line 6582 "parser.tab.c"
    break;

  case 405: /* file_info: "," name  */
#line 1498 "parser.y"
           { (yyval.data) = Tptp_mk_FileInfo_name((yyvsp[0].data)); }
#line 6588 "parser.tab.c"
    break;

  case 406: /* file_info: %empty  */
#line 1499 "parser.y"
           { (yyval.data) = Tptp_mk_FileInfo_nothing; }
#line 6594 "parser.tab.c"
    break;

  case 407: /* theory: "theory(" theory_name optional_info ")"  */
#line 1503 "parser.y"
                                          { (yyval.data) = Tptp_mk_Theory_mk((yyvsp[-2].data), (yyvsp[-1].data)); }
#line 6600 "parser.tab.c"
    break;

  case 408: /* theory_name: atomic_word  */
#line 1507 "parser.y"
              { (yyval.data) = Tptp_mk_TheoryName_mk((yyvsp[0].data)); }
#line 6606 "parser.tab.c"
    break;

  case 409: /* creator_source: "creator(" creator_name "," useful_info "," parents ")"  */
#line 1511 "parser.y"
                                                          { (yyval.data) = Tptp_mk_CreatorSource_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6612 "parser.tab.c"
    break;

  case 410: /* creator_name: atomic_word  */
#line 1515 "parser.y"
              { (yyval.data) = Tptp_mk_CreatorName_mk((yyvsp[0].data)); }
#line 6618 "parser.tab.c"
    break;

  case 411: /* parents: "[]"  */
#line 1519 "parser.y"
       { (yyval.data) = Tptp_mk_Parents_empty; }
#line 6624 "parser.tab.c"
    break;

  case 412: /* parents: "[" parent_list "]"  */
#line 1520 "parser.y"
                        { (yyval.data) = Tptp_mk_Parents_parentList((yyvsp[-1].data)); }
#line 6630 "parser.tab.c"
    break;

  case 413: /* parent_list: parent_info comma_parent_info_list  */
#line 1524 "parser.y"
                                     { (yyval.data) = Tptp_mk_ParentList_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 6636 "parser.tab.c"
    break;

  case 414: /* comma_parent_info_list: %empty  */
#line 1528 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 6642 "parser.tab.c"
    break;

  case 415: /* comma_parent_info_list: comma_parent_info_list comma_parent_info  */
#line 1529 "parser.y"
                                             { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 6648 "parser.tab.c"
    break;

  case 416: /* comma_parent_info: "," parent_info  */
#line 1533 "parser.y"
                  { (yyval.data) = Tptp_mk_CommaParentInfo_mk((yyvsp[0].data)); }
#line 6654 "parser.tab.c"
    break;

  case 417: /* parent_info: source parent_details  */
#line 1537 "parser.y"
                        { (yyval.data) = Tptp_mk_ParentInfo_mk((yyvsp[-1].data), (yyvsp[0].data)); }
#line 6660 "parser.tab.c"
    break;

  case 418: /* parent_details: ":" general_term  */
#line 1541 "parser.y"
                   { (yyval.data) = Tptp_mk_ParentDetails_generalTerm((yyvsp[0].data)); }
#line 6666 "parser.tab.c"
    break;

  case 419: /* parent_details: %empty  */
#line 1542 "parser.y"
           { (yyval.data) = Tptp_mk_ParentDetails_nothing; }
#line 6672 "parser.tab.c"
    break;

  case 420: /* optional_info: "," useful_info  */
#line 1546 "parser.y"
                  { (yyval.data) = Tptp_mk_OptionalInfo_usefulInfo((yyvsp[0].data)); }
#line 6678 "parser.tab.c"
    break;

  case 421: /* optional_info: %empty  */
#line 1547 "parser.y"
           { (yyval.data) = Tptp_mk_OptionalInfo_nothing; }
#line 6684 "parser.tab.c"
    break;

  case 422: /* useful_info: general_list  */
#line 1551 "parser.y"
               { (yyval.data) = Tptp_mk_UsefulInfo_mk((yyvsp[0].data)); }
#line 6690 "parser.tab.c"
    break;

  case 423: /* include: "include(" file_name include_optionals ")."  */
#line 1555 "parser.y"
                                              { (yyval.data) = Tptp_mk_Include_mk((yyvsp[-2].data), (yyvsp[-1].data)); }
#line 6696 "parser.tab.c"
    break;

  case 424: /* include_optionals: %empty  */
#line 1559 "parser.y"
         {(yyval.data) = Tptp_mk_IncludeOptionals_nothing; }
#line 6702 "parser.tab.c"
    break;

  case 425: /* include_optionals: "," formula_selection  */
#line 1560 "parser.y"
                          { (yyval.data) = Tptp_mk_IncludeOptionals_formulaSelection((yyvsp[0].data)); }
#line 6708 "parser.tab.c"
    break;

  case 426: /* include_optionals: "," formula_selection "," space_name  */
#line 1561 "parser.y"
                                         { (yyval.data) = Tptp_mk_IncludeOptionals_formulaSelectionSpaceName((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6714 "parser.tab.c"
    break;

  case 427: /* formula_selection: "[" name_list "]"  */
#line 1565 "parser.y"
                    { (yyval.data) = Tptp_mk_FormulaSelection_nameList((yyvsp[-1].data)); }
#line 6720 "parser.tab.c"
    break;

  case 428: /* formula_selection: "*"  */
#line 1566 "parser.y"
         { (yyval.data) = Tptp_mk_FormulaSelection_star; }
#line 6726 "parser.tab.c"
    break;

  case 429: /* name_list: name  */
#line 1570 "parser.y"
       { (yyval.data) = Tptp_mk_NameList_name((yyvsp[0].data)); }
#line 6732 "parser.tab.c"
    break;

  case 430: /* name_list: name "," name_list  */
#line 1571 "parser.y"
                       { (yyval.data) = Tptp_mk_NameList_nameNameList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6738 "parser.tab.c"
    break;

  case 431: /* space_name: name  */
#line 1575 "parser.y"
       { (yyval.data) = Tptp_mk_SpaceName_mk((yyvsp[0].data)); }
#line 6744 "parser.tab.c"
    break;

  case 432: /* general_term: general_data  */
#line 1579 "parser.y"
               { (yyval.data) = Tptp_mk_GeneralTerm_generalData((yyvsp[0].data)); }
#line 6750 "parser.tab.c"
    break;

  case 433: /* general_term: general_data ":" general_term  */
#line 1580 "parser.y"
                                  { (yyval.data) = Tptp_mk_GeneralTerm_generalDataGeneralTerm((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6756 "parser.tab.c"
    break;

  case 434: /* general_term: general_list  */
#line 1581 "parser.y"
                 { (yyval.data) = Tptp_mk_GeneralTerm_generalList((yyvsp[0].data)); }
#line 6762 "parser.tab.c"
    break;

  case 435: /* general_data: atomic_word  */
#line 1585 "parser.y"
              { (yyval.data) = Tptp_mk_GeneralData_atomicWord((yyvsp[0].data)); }
#line 6768 "parser.tab.c"
    break;

  case 436: /* general_data: general_function  */
#line 1586 "parser.y"
                     { (yyval.data) = Tptp_mk_GeneralData_generalFunction((yyvsp[0].data)); }
#line 6774 "parser.tab.c"
    break;

  case 437: /* general_data: variable  */
#line 1587 "parser.y"
             { (yyval.data) = Tptp_mk_GeneralData_variable((yyvsp[0].data)); }
#line 6780 "parser.tab.c"
    break;

  case 438: /* general_data: number  */
#line 1588 "parser.y"
           { (yyval.data) = Tptp_mk_GeneralData_number((yyvsp[0].data)); }
#line 6786 "parser.tab.c"
    break;

  case 439: /* general_data: distinct_object  */
#line 1589 "parser.y"
                    { (yyval.data) = Tptp_mk_GeneralData_distinctObject((yyvsp[0].data)); }
#line 6792 "parser.tab.c"
    break;

  case 440: /* general_data: formula_data  */
#line 1590 "parser.y"
                 { (yyval.data) = Tptp_mk_GeneralData_formulaData((yyvsp[0].data)); }
#line 6798 "parser.tab.c"
    break;

  case 441: /* general_function: atomic_word "(" general_terms ")"  */
#line 1594 "parser.y"
                                    { (yyval.data) = Tptp_mk_GeneralFunction_mk((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6804 "parser.tab.c"
    break;

  case 442: /* formula_data: "$thf(" thf_formula ")"  */
#line 1598 "parser.y"
                          { (yyval.data) = Tptp_mk_FormulaData_thfFormula((yyvsp[-1].data)); }
#line 6810 "parser.tab.c"
    break;

  case 443: /* formula_data: "$tff(" tff_formula ")"  */
#line 1599 "parser.y"
                            { (yyval.data) = Tptp_mk_FormulaData_tffFormula((yyvsp[-1].data)); }
#line 6816 "parser.tab.c"
    break;

  case 444: /* formula_data: "$fof(" fof_formula ")"  */
#line 1600 "parser.y"
                            { (yyval.data) = Tptp_mk_FormulaData_fofFormula((yyvsp[-1].data)); }
#line 6822 "parser.tab.c"
    break;

  case 445: /* formula_data: "$cnf(" cnf_formula ")"  */
#line 1601 "parser.y"
                            { (yyval.data) = Tptp_mk_FormulaData_cnfFormula((yyvsp[-1].data)); }
#line 6828 "parser.tab.c"
    break;

  case 446: /* formula_data: "$fot(" fof_term ")"  */
#line 1602 "parser.y"
                         { (yyval.data) = Tptp_mk_FormulaData_fofTerm((yyvsp[-1].data)); }
#line 6834 "parser.tab.c"
    break;

  case 447: /* general_list: "[]"  */
#line 1606 "parser.y"
       { (yyval.data) = Tptp_mk_GeneralList_empty; }
#line 6840 "parser.tab.c"
    break;

  case 448: /* general_list: "[" general_terms "]"  */
#line 1607 "parser.y"
                          { (yyval.data) = Tptp_mk_GeneralList_generalTerms((yyvsp[-1].data)); }
#line 6846 "parser.tab.c"
    break;

  case 449: /* general_terms: general_term comma_general_term_list  */
#line 1611 "parser.y"
                                       { (yyval.data) = Tptp_mk_GeneralTerms_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 6852 "parser.tab.c"
    break;

  case 450: /* comma_general_term_list: %empty  */
#line 1615 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 6858 "parser.tab.c"
    break;

  case 451: /* comma_general_term_list: comma_general_term_list comma_general_term  */
#line 1616 "parser.y"
                                               { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 6864 "parser.tab.c"
    break;

  case 452: /* comma_general_term: "," general_term  */
#line 1620 "parser.y"
                   { (yyval.data) = Tptp_mk_CommaGeneralTerm_mk((yyvsp[0].data)); }
#line 6870 "parser.tab.c"
    break;

  case 453: /* name: atomic_word  */
#line 1624 "parser.y"
              { (yyval.data) = Tptp_mk_Name_atomicWord((yyvsp[0].data)); }
#line 6876 "parser.tab.c"
    break;

  case 454: /* name: integer  */
#line 1625 "parser.y"
            { (yyval.data) = Tptp_mk_Name_integer((yyvsp[0].data)); }
#line 6882 "parser.tab.c"
    break;

  case 455: /* lower_word: "unknown"  */
#line 1629 "parser.y"
          { (yyval.data) = Tptp_mk_LowerWord_mk(lean_mk_string("unknown")); }
#line 6888 "parser.tab.c"
    break;

  case 456: /* lower_word: LOWER_WORD  */
#line 1630 "parser.y"
               { (yyval.data) = Tptp_mk_LowerWord_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6894 "parser.tab.c"
    break;

  case 457: /* single_quoted: SINGLE_QUOTED  */
#line 1634 "parser.y"
                { (yyval.data) = Tptp_mk_SingleQuoted_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6900 "parser.tab.c"
    break;

  case 458: /* back_quoted: BACK_QUOTED  */
#line 1638 "parser.y"
              { (yyval.data) = Tptp_mk_BackQuoted_mk(Tptp_mk_UpperWord_mk(lean_mk_string((yyvsp[0].raw)))); free((yyvsp[0].raw)); }
#line 6906 "parser.tab.c"
    break;

  case 459: /* atomic_word: lower_word  */
#line 1642 "parser.y"
             { (yyval.data) = Tptp_mk_AtomicWord_lowerWord((yyvsp[0].data)); }
#line 6912 "parser.tab.c"
    break;

  case 460: /* atomic_word: single_quoted  */
#line 1643 "parser.y"
                  { (yyval.data) = Tptp_mk_AtomicWord_singleQuoted((yyvsp[0].data)); }
#line 6918 "parser.tab.c"
    break;

  case 461: /* atomic_word: back_quoted  */
#line 1644 "parser.y"
                { (yyval.data) = Tptp_mk_AtomicWord_backQuoted((yyvsp[0].data)); }
#line 6924 "parser.tab.c"
    break;

  case 462: /* dollar_word: DOLLAR_WORD  */
#line 1648 "parser.y"
              { (yyval.data) = Tptp_mk_DollarWord_mk(lean_mk_string((yyvsp[0].raw))) ; free((yyvsp[0].raw)); }
#line 6930 "parser.tab.c"
    break;

  case 463: /* dollar_dollar_word: DOLLAR_DOLLAR_WORD  */
#line 1652 "parser.y"
                     { (yyval.data) = Tptp_mk_DollarDollarWord_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6936 "parser.tab.c"
    break;

  case 464: /* atomic_defined_word: dollar_word  */
#line 1656 "parser.y"
              { (yyval.data) = Tptp_mk_AtomicDefinedWord_mk((yyvsp[0].data)); }
#line 6942 "parser.tab.c"
    break;

  case 465: /* atomic_system_word: dollar_dollar_word  */
#line 1660 "parser.y"
                     { (yyval.data) = Tptp_mk_AtomicSystemWord_mk((yyvsp[0].data)); }
#line 6948 "parser.tab.c"
    break;

  case 466: /* integer: INTEGER  */
#line 1664 "parser.y"
          { (yyval.data) = parse_integer((yyvsp[0].raw)); free((yyvsp[0].raw)); }
#line 6954 "parser.tab.c"
    break;

  case 467: /* rational: RATIONAL  */
#line 1668 "parser.y"
           { (yyval.data) = parse_rational((yyvsp[0].raw)); free((yyvsp[0].raw)); }
#line 6960 "parser.tab.c"
    break;

  case 468: /* real: REAL  */
#line 1672 "parser.y"
       { (yyval.data) = parse_real((yyvsp[0].raw)); free((yyvsp[0].raw)); }
#line 6966 "parser.tab.c"
    break;

  case 469: /* number: integer  */
#line 1676 "parser.y"
          { (yyval.data) = Tptp_mk_Number_integer((yyvsp[0].data)); }
#line 6972 "parser.tab.c"
    break;

  case 470: /* number: rational  */
#line 1677 "parser.y"
             { (yyval.data) = Tptp_mk_Number_rational((yyvsp[0].data)); }
#line 6978 "parser.tab.c"
    break;

  case 471: /* number: real  */
#line 1678 "parser.y"
         { (yyval.data) = Tptp_mk_Number_real((yyvsp[0].data)); }
#line 6984 "parser.tab.c"
    break;

  case 472: /* file_name: atomic_word  */
#line 1682 "parser.y"
              { (yyval.data) = Tptp_mk_FileName_mk((yyvsp[0].data)); }
#line 6990 "parser.tab.c"
    break;


#line 6994 "parser.tab.c"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == TOK_YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      yyerror (scanner, context, YY_("syntax error"));
    }

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= TOK_YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == TOK_YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, scanner, context);
          yychar = TOK_YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp, scanner, context);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (scanner, context, YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != TOK_YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, scanner, context);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp, scanner, context);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif

  return yyresult;
}

#line 1685 "parser.y"


void yyerror(yyscan_t scanner, TptpParseContext *context, const char *message) {
  (void)scanner;
  (void)message;
  context->error = true;
}
