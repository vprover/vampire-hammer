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
#define YYLAST   3157

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  80
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  249
/* YYNRULES -- Number of rules.  */
#define YYNRULES  467
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  809

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
       0,   437,   437,   441,   445,   446,   450,   451,   455,   456,
     457,   458,   459,   460,   464,   468,   472,   476,   480,   484,
     488,   492,   493,   497,   498,   502,   503,   504,   508,   509,
     510,   511,   512,   513,   517,   518,   519,   523,   527,   528,
     529,   533,   534,   538,   539,   543,   544,   548,   549,   550,
     554,   555,   559,   560,   561,   562,   566,   570,   574,   575,
     579,   583,   584,   588,   592,   596,   597,   598,   599,   603,
     604,   608,   609,   610,   611,   612,   616,   617,   621,   625,
     629,   633,   634,   638,   639,   643,   644,   648,   652,   653,
     657,   658,   659,   663,   664,   665,   666,   667,   671,   672,
     676,   677,   678,   682,   686,   690,   691,   695,   699,   700,
     704,   705,   706,   710,   714,   718,   719,   720,   724,   725,
     729,   730,   734,   735,   739,   743,   747,   751,   752,   753,
     757,   758,   759,   760,   761,   762,   766,   767,   771,   775,
     776,   780,   781,   785,   786,   790,   791,   792,   796,   797,
     801,   802,   803,   804,   808,   812,   816,   817,   821,   822,
     826,   830,   831,   835,   839,   843,   844,   845,   849,   850,
     854,   858,   859,   860,   861,   865,   869,   870,   874,   878,
     879,   883,   884,   888,   889,   893,   897,   898,   902,   903,
     907,   911,   912,   913,   917,   918,   919,   920,   921,   925,
     926,   930,   934,   935,   939,   943,   944,   948,   949,   953,
     954,   955,   959,   963,   964,   965,   969,   970,   974,   975,
     976,   977,   978,   979,   983,   984,   988,   992,   993,   997,
    1001,  1002,  1006,  1010,  1014,  1018,  1019,  1023,  1024,  1028,
    1029,  1033,  1037,  1038,  1042,  1043,  1047,  1048,  1052,  1056,
    1060,  1064,  1065,  1066,  1067,  1071,  1072,  1076,  1077,  1081,
    1085,  1086,  1090,  1091,  1092,  1096,  1097,  1101,  1105,  1106,
    1110,  1111,  1115,  1116,  1120,  1121,  1125,  1129,  1130,  1134,
    1135,  1136,  1140,  1144,  1145,  1149,  1150,  1151,  1155,  1159,
    1160,  1164,  1168,  1172,  1176,  1177,  1181,  1182,  1186,  1190,
    1191,  1195,  1196,  1200,  1201,  1205,  1206,  1210,  1211,  1212,
    1216,  1217,  1221,  1222,  1226,  1230,  1231,  1235,  1239,  1240,
    1244,  1245,  1249,  1250,  1251,  1252,  1256,  1257,  1258,  1262,
    1263,  1267,  1268,  1269,  1273,  1274,  1278,  1282,  1283,  1287,
    1288,  1292,  1293,  1297,  1298,  1299,  1300,  1301,  1302,  1306,
    1307,  1311,  1315,  1319,  1323,  1327,  1331,  1335,  1339,  1340,
    1344,  1345,  1349,  1353,  1357,  1361,  1365,  1369,  1373,  1377,
    1381,  1385,  1386,  1390,  1391,  1392,  1393,  1394,  1398,  1402,
    1403,  1407,  1411,  1416,  1417,  1418,  1419,  1420,  1424,  1425,
    1429,  1430,  1434,  1438,  1442,  1446,  1450,  1451,  1452,  1456,
    1460,  1461,  1465,  1469,  1473,  1477,  1481,  1482,  1486,  1490,
    1491,  1495,  1499,  1503,  1504,  1508,  1509,  1513,  1517,  1521,
    1522,  1523,  1527,  1528,  1532,  1533,  1537,  1541,  1542,  1543,
    1547,  1548,  1549,  1550,  1551,  1552,  1556,  1560,  1561,  1562,
    1563,  1564,  1568,  1569,  1573,  1577,  1578,  1582,  1586,  1587,
    1591,  1592,  1596,  1600,  1604,  1605,  1606,  1610,  1614,  1618,
    1622,  1626,  1630,  1634,  1638,  1639,  1640,  1644
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

#define YYPACT_NINF (-534)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-362)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
    -534,   130,  -534,  1181,  -534,   554,   554,   660,   554,   554,
     554,   554,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,
    -534,  -534,  -534,  -534,  -534,  -534,   104,  -534,  -534,  -534,
    -534,  -534,   108,  -534,   111,   127,   131,   154,   166,    90,
      90,    50,   183,    90,    90,    90,    90,   193,   196,   212,
     554,  -534,   217,  -534,   232,   263,   268,   303,   823,  2665,
    2375,   176,   320,   554,  1823,  1573,  2266,  2375,  -534,  -534,
    -534,  -534,  -534,  -534,   823,  1147,  -534,  -534,  -534,  -534,
    -534,  -534,  -534,   201,  -534,  -534,   305,   333,   336,  -534,
     339,   162,  -534,  -534,   314,  -534,   372,  -534,   377,  -534,
    -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,
    -534,  -534,   823,  2375,  2097,  1573,  2266,  2665,  -534,  -534,
    -534,  -534,   346,  -534,  -534,  -534,   399,  -534,  -534,  2375,
    -534,  1367,  -534,  -534,   339,  -534,  -534,  -534,  -534,   345,
     451,   246,  -534,  1032,   527,  -534,  -534,  -534,   396,   443,
    1367,  -534,   554,  -534,  -534,   448,  2011,  -534,   339,  -534,
    -534,  -534,   476,   477,   505,   497,  1573,  -534,  1897,  -534,
    -534,   112,  -534,   511,  -534,   339,  -534,  -534,  -534,  -534,
     456,   537,  1162,   900,  -534,  -534,   953,  -534,  -534,   146,
    -534,  -534,  -534,  1089,  -534,  -534,  -534,   336,   396,  -534,
    -534,  -534,  -534,   519,  -534,  2151,   517,  -534,  -534,    67,
     231,   545,  -534,   549,   245,   550,  -534,   355,  -534,  -534,
     786,  2734,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  2818,
    -534,  -534,   112,   339,  -534,  -534,  -534,  -534,   501,   560,
     532,   980,   922,  -534,  2818,   644,  -534,  -534,   153,  -534,
    -534,  -534,   886,  -534,  -534,   336,   396,  -534,  -534,    33,
    -534,  -534,   507,   523,  -534,  -534,  -534,  -534,  -534,   553,
    3001,  -534,  -534,  -534,  -534,   437,   231,   581,  -534,   583,
     245,   585,  -534,  -534,   356,   339,  -534,   587,  2097,  -534,
     579,  -534,  -534,  2097,  -534,  2097,  1029,   592,  1733,  2097,
    2097,  2097,   600,   602,  -534,  -534,  -534,   603,   604,   611,
    -534,   573,  2665,  2665,   616,   620,  1367,  -534,   577,   630,
    1367,  1367,  1367,  -534,  -534,  -534,  -534,   586,  -534,  1367,
    1367,  -534,   404,   639,  -534,  -534,  -534,  -534,   639,   632,
     635,   528,   309,   309,   650,  -534,  -534,  -534,  -534,  -534,
     661,  1897,  -534,  -534,   343,   636,  -534,  -534,   382,    49,
    -534,  -534,  -534,  -534,   618,   659,  1897,  1897,  1897,  1897,
    1897,  -534,  1897,  1597,  1597,   435,   667,  1897,  -534,  -534,
    -534,  -534,  -534,   639,  -534,   422,  1897,  1897,  1897,   434,
     434,   665,  -534,   668,  -534,   586,  -534,   674,   677,   682,
    3001,  -534,  -534,  -534,  -534,  2921,  -534,   657,  -534,  -534,
     105,   685,  2818,  2818,  2818,  2818,  2818,  2818,  2818,  -534,
    -534,  -534,   395,  -534,  -534,  2818,  2578,  2578,   466,  1745,
    1745,  1745,  1745,  1745,   639,  2921,  -534,  -534,  -534,  -534,
    -534,  2818,   422,  2818,  2818,  2818,   691,  -534,   693,  -534,
    -534,  1029,   660,   660,   660,   660,   660,  -534,   696,  -534,
    -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,   701,
     700,   705,   709,  -534,  -534,  -534,  -534,  -534,   710,  -534,
    -534,   714,  -534,  -534,   713,  -534,  -534,  -534,  -534,  -534,
    -534,  -534,  -534,  -534,   689,   716,   698,   718,  -534,   720,
    -534,  -534,   528,   528,  -534,  -534,  -534,   684,   686,  -534,
    -534,   711,  -534,   739,  -534,  -534,  -534,  -534,   719,   736,
     119,   415,   745,  -534,   717,  -534,  -534,  -534,  -534,  -534,
    -534,   417,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  1897,
    -534,  -534,  -534,  -534,  -534,  1897,   750,   729,  -534,  -534,
    -534,   761,   762,   765,   743,   769,  3078,   420,  -534,  -534,
     770,  -534,  1412,  -534,  -534,  -534,  -534,  -534,  -534,  -534,
    -534,  -534,  -534,  2921,  -534,  -534,  -534,  -534,  -534,  -534,
     725,  -534,  -534,  -534,  -534,  -534,   749,   782,   779,   787,
     532,   723,   774,  -534,   725,  -534,  -534,  -534,   788,  -534,
     789,   794,  -534,  -534,   795,   791,   811,  -534,   813,   817,
    -534,   820,  -534,   696,  -534,   469,  -534,  -534,  2097,  -534,
    -534,  2665,  -534,  -534,  1367,  -534,   790,   639,   818,   639,
     584,   824,   458,   827,    78,   829,   806,   584,   639,   584,
    -534,   309,  1897,  -534,   833,  -534,   838,  -534,  1897,  -534,
    1597,   834,  -534,   847,   848,  -534,  -534,   837,   850,  -534,
     854,  -534,  -534,  -534,  -534,   434,  2818,   838,   851,  -534,
    2818,  -534,  2458,   834,  -534,   860,   861,  -534,  -534,   871,
     865,   639,  2818,  -534,  -534,  -534,  -534,  1029,  -534,   469,
     554,   878,   469,   469,   879,  -534,  -534,  -534,  -534,  -534,
    1367,  -534,  2174,  -534,   584,  -534,  -534,   584,  -534,  -534,
     584,   528,  -534,  -534,   852,   887,   881,  -534,   884,   890,
     870,   405,  1897,  -534,  1897,  -534,  -534,  -534,   717,  -534,
    -534,  1897,  -534,   838,   896,   885,  2818,  2818,  -534,  -534,
    -534,  1412,  -534,  -534,  -534,  -534,  -534,   912,  -534,  -534,
     913,   916,  -534,  -534,  -534,   827,  -534,  -534,  -534,   924,
     584,  -534,   538,  -534,   932,  -534,  -534,  -534,  2818,  -534,
    -534,   934,  -534,   498,   498,   498,  1251,  -534,  -534,  -534,
    -534,  -534,  1029,  -534,   937,   939,   940,   835,  -534,  -534,
    -534,   944,   918,  -534,  -534,  -534,  -534,   835,   957,  2665,
    -534,  -534,   955,   908,  -534,  -534,  1029,  -534,  -534
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int16 yydefact[] =
{
       4,     0,     2,     3,     1,     0,     0,     0,     0,     0,
       0,     0,     5,     6,    13,     8,     9,    10,    11,    12,
       7,   452,   453,   451,   461,   450,     0,   454,   455,   456,
     448,   449,     0,   467,   419,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    23,     0,
       0,   423,   420,   418,     0,     0,     0,     0,     0,     0,
       0,     0,   424,     0,     0,     0,     0,     0,   378,   457,
     458,   381,   463,   462,     0,     0,   325,   322,   285,   286,
     289,   290,   287,   288,   308,   297,   291,   293,     0,   305,
      22,   318,   320,   294,   365,   299,   367,   301,   369,   380,
     296,   382,   306,   366,   459,   460,   368,   370,   464,   465,
     466,   379,     0,     0,     0,     0,     0,     0,   442,   434,
     432,    24,   427,   431,   435,   429,   430,   433,   341,     0,
     342,     0,   312,   351,    22,   260,   262,   265,   266,   268,
     269,   278,   275,     0,   277,   279,   280,   261,     0,     0,
       0,   422,     0,   421,   426,     0,     0,   256,    22,   255,
     257,   258,     0,   294,   301,     0,     0,   254,     0,   251,
     199,     0,   253,     0,   340,    22,   127,   132,   136,   137,
     139,   140,     0,   145,   152,   150,   146,   161,   162,   151,
     165,   166,   170,   147,   167,   174,   173,     0,   196,   128,
     129,   134,   135,     0,   338,     0,     0,   339,   337,     0,
     168,   365,   171,   367,   176,   369,   195,   154,   373,   334,
       0,     0,   335,   374,   332,   333,   377,   375,   376,     0,
      98,   331,     0,    22,    25,    30,    34,    35,    38,    39,
      40,     0,    47,    52,     0,    48,    61,    62,    53,    65,
      66,    72,    49,    67,    75,     0,    70,    68,    26,     0,
      36,   115,   116,   117,    27,    32,    33,    74,   330,     0,
       0,   327,   328,   326,   329,     0,    69,   365,    71,   367,
      79,   369,    77,    76,    54,    22,    15,     0,     0,   323,
       0,   364,   363,     0,   362,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   307,   298,   309,     0,     0,     0,
     445,     0,     0,     0,     0,     0,     0,   315,     0,     0,
       0,     0,     0,   345,   343,   346,   344,     0,   348,     0,
       0,   352,     0,     0,   278,   274,   277,   425,     0,     0,
       0,     0,     0,     0,     0,   179,   360,   365,   361,   369,
       0,     0,   191,   202,   193,     0,   168,   176,   192,     0,
     371,   367,   372,   249,     0,     0,     0,     0,     0,     0,
       0,   354,     0,     0,     0,     0,     0,     0,   163,   148,
     149,   151,   154,     0,   336,     0,     0,     0,     0,     0,
       0,     0,    81,     0,   350,   351,   349,     0,     0,     0,
      97,    93,    94,    95,    96,     0,   105,     0,    69,    79,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    56,
      47,    48,    53,    49,    70,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    63,    50,    51,    53,
      54,     0,     0,     0,     0,     0,     0,   319,     0,   292,
     276,     0,     0,     0,     0,     0,     0,   383,   416,   384,
     391,   385,   386,   396,   397,   398,   390,    20,   321,     0,
     303,     0,     0,   440,   439,   441,   438,   437,   444,   443,
     428,     0,   281,   311,   314,   313,    19,   271,   273,   272,
     347,   270,   267,   310,     0,   283,     0,   156,   158,   159,
     206,    18,     0,     0,   205,   208,   210,     0,   207,   209,
     223,     0,   218,   355,   219,   220,   356,   357,     0,   181,
       0,   153,   201,   200,     0,   242,   252,    17,   142,   145,
     146,   151,   147,   196,   144,   143,   141,   138,   233,     0,
     194,   175,   197,   164,   234,     0,     0,     0,   232,   358,
     359,     0,     0,     0,     0,    83,     0,    55,    73,   109,
     104,    99,     0,   235,    16,    42,    44,    46,    43,    45,
      41,    37,   125,     0,    90,    78,    91,    64,   126,   113,
     118,   119,   120,   122,   121,   123,     0,    58,     0,     0,
     114,     0,   113,   108,   110,   112,   111,   124,     0,   103,
       0,     0,    14,   324,   388,     0,     0,   405,   401,     0,
     393,     0,   395,   416,   403,     0,    21,   295,     0,   300,
     302,     0,   446,   436,     0,   316,     0,     0,     0,     0,
       0,     0,     0,   216,     0,   230,     0,     0,     0,     0,
     180,     0,     0,   186,     0,   183,     0,   187,     0,   203,
       0,     0,   248,     0,   244,   247,   246,     0,     0,   153,
       0,   169,   172,   177,    82,     0,     0,     0,     0,    85,
       0,   106,     0,     0,   241,     0,   237,   240,   239,     0,
       0,     0,     0,    55,   100,   101,   102,     0,   387,     0,
       0,     0,     0,     0,     0,   415,   417,   304,   447,   317,
       0,   284,     0,   157,     0,   160,   211,     0,   222,   217,
       0,     0,   229,   226,     0,   224,     0,   182,   165,   188,
       0,   193,     0,   353,     0,   204,   250,   243,     0,   198,
     190,     0,    84,   105,    88,     0,     0,     0,   107,    97,
     236,     0,    92,    57,    59,    60,   389,     0,   400,   399,
       0,     0,   402,   282,   259,     0,   227,   228,   231,     0,
       0,   221,     0,   184,     0,   185,   245,   155,     0,    86,
      87,     0,   238,     0,     0,     0,     0,   225,   189,   178,
      89,    80,     0,   406,     0,     0,     0,     0,   215,   212,
     213,   414,     0,   409,   404,   392,   394,     0,     0,     0,
     412,   407,   408,     0,   214,   413,     0,   410,   411
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,
    -534,  -534,  -534,   353,   735,   876,    68,  -534,  -534,  -534,
    -534,  -534,  -377,   -87,  -534,  1117,  -534,  -534,   312,  -534,
      66,  -187,  -534,   452,  -534,  -534,  -534,   520,  -534,  -534,
    -534,   329,  -534,   439,   228,   -74,  -534,    80,  -534,   -61,
    -214,  -534,  -534,  -151,   322,  -316,  -534,  -534,  -345,  -534,
    -534,  -534,  -533,  -534,   883,    16,  -534,  -534,  -534,  -534,
    -534,  -291,  -534,  -169,  -534,  -534,  -274,  -534,  -534,  -218,
     797,  -534,  -111,  -469,  -534,  -534,  -204,  -534,  -534,  -534,
     364,  -534,   486,  -534,   247,  -534,  -313,  -288,    94,  -243,
    -534,  -534,   -44,   670,   506,   237,  -534,  -440,   316,   255,
     235,  -534,  -534,   308,  -534,  -505,  -534,  -534,   283,  -534,
    -534,  -534,   299,  -534,  -534,   799,  -507,   796,  -534,   327,
    -534,    25,   -98,  -534,  -534,  -534,  -534,  -534,  -141,   -21,
    -115,  -101,  -534,   409,   -14,  -534,  -534,  -534,  -534,  -534,
     -68,  -534,  -534,   -48,    22,  -253,   -51,  -534,   910,   708,
    -534,  -534,  -534,   207,  -534,   744,  -534,  -181,  -534,  -299,
     771,  -534,   844,   -26,   -50,  -534,   742,   -66,   401,  -231,
    -534,  -534,  -534,   606,    -9,  -102,    79,   -20,   601,   970,
    1822,  2191,  1339,  1708,  -534,  -534,   -45,  2337,  -534,   -27,
    -266,   363,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,
    -534,  -534,  -534,  -534,  -309,  -534,  -534,  -534,   250,  -534,
     438,  -410,  -534,  -534,  -534,   905,  -534,   -41,  -534,  -534,
    -534,  -518,   746,  -534,  -534,    17,   605,  -534,  -534,    -5,
    -534,  -534,  -215,  -534,     2,  -534,  -534,   -43,   607
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
       0,     1,     2,     3,    12,    13,    14,   285,    15,    16,
      17,    18,    19,   297,    47,   233,   406,   235,   236,   237,
     238,   239,   240,   241,   436,   242,   243,   244,   586,   587,
     245,   246,   247,   248,   249,   250,   251,   252,   253,   254,
     391,   554,   668,   734,   735,   255,   398,   424,   257,   598,
     599,   560,   671,   258,   593,   259,   595,   260,   261,   262,
     263,   264,   265,   266,   175,   352,   177,   178,   179,   180,
     181,   182,   378,   183,   184,   185,   496,   497,   498,   186,
     187,   188,   189,   190,   191,   192,   193,   194,   195,   344,
     518,   644,   719,   646,   720,   196,   353,   197,   354,   355,
     522,   649,   339,   635,   505,   506,   789,   507,   508,   716,
     509,   634,   510,   636,   200,   201,   202,   267,   675,   676,
     677,   203,   653,   654,   655,   359,   656,   268,   158,   159,
     160,   134,   135,   136,   137,   138,   139,   140,   141,   142,
     143,   144,   145,   494,   146,    78,    79,    80,    81,    82,
      83,    84,    85,    86,    87,   469,    88,    89,   147,   148,
     318,   484,   625,   161,    91,    92,   269,   270,   271,   272,
     385,   205,   273,   207,   401,   402,   274,   375,   736,   372,
     512,   513,   514,   548,   162,   293,   403,   404,   408,   277,
     278,   279,   409,   281,   363,   282,    99,   283,   101,   102,
     604,   605,   459,   460,   609,   461,   611,   462,   463,   691,
     464,   613,   465,   606,   784,   792,   802,   807,   793,   800,
     616,   695,    20,    42,    52,    61,   153,   310,   122,   123,
     124,   125,   311,   478,   622,   466,    27,    28,    29,   103,
     104,   105,   106,   107,   108,   109,   110,   111,    34
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      30,    30,    33,    30,    30,    30,    30,    31,    31,   334,
      31,    31,    31,    31,   119,   407,   127,   425,   121,   652,
     157,   199,    26,    32,   290,    35,    36,    37,    38,   674,
     458,   314,   120,   317,   149,   335,   379,    76,   217,   284,
     400,   149,   511,    76,    77,    30,   304,   471,   472,   336,
      77,   643,    31,    76,   126,   678,   209,   275,    30,   538,
      77,   289,   632,   307,   590,    31,   305,    62,   295,   392,
     399,   199,   119,   524,   127,   528,   534,   535,   536,   537,
     154,   176,   332,   438,   581,   541,   543,   149,   217,   284,
     120,    76,   286,   330,   381,   373,   596,   696,    77,    23,
     341,    50,   384,   149,   709,   149,   209,   275,   429,   547,
     430,   431,   126,   580,   582,   583,   584,   585,    69,    70,
     525,   345,    21,    22,   149,   594,   517,    51,    23,   562,
       4,   176,   370,    39,   234,    76,   306,    40,   303,   217,
      41,   217,    77,   551,   552,   553,   256,    30,   530,   530,
     530,   530,   530,   426,    31,   710,    43,   419,    25,   198,
      44,  -194,   532,   532,   532,   532,   532,   294,   -90,    62,
     642,   696,   170,   718,   696,   696,   563,   374,   382,   334,
     334,   334,   350,    45,   234,  -194,   371,    25,   334,   334,
     428,   418,   -90,   371,   284,    46,   256,   529,   529,   529,
     529,   529,   284,   511,   511,   487,   488,   489,   674,   198,
      53,   393,   393,   438,   491,   492,  -307,   284,   314,   336,
     336,   336,    58,   652,   400,   304,    59,   304,   336,   336,
     151,   304,   304,   304,   678,   427,   298,   290,   399,   555,
    -307,    60,   449,   440,   450,   305,    63,   305,   470,   470,
     470,   305,   305,   305,   400,   531,   531,   531,   531,   531,
     198,    64,   540,   540,  -360,    90,  -360,   119,   119,   127,
     127,   480,  -263,  -263,   448,  -263,   294,    76,  -361,   747,
    -361,   287,   750,   751,    77,   120,   120,   517,   517,   397,
     149,    30,    65,   643,   149,   149,   149,    66,    31,   519,
    -263,   256,   658,   149,   149,   590,   495,   126,   126,   256,
     421,   499,    21,    22,   515,   306,    70,   306,    23,   302,
    -298,   306,   306,   306,   217,   565,   566,   567,   568,   569,
     570,   571,    67,   342,   294,   725,   516,   596,   299,   217,
     217,   217,   217,   217,  -298,   217,   542,   542,  -309,   152,
     217,   291,   575,   577,   591,   703,   499,   803,  -196,   217,
     217,   217,   726,   287,   714,   697,   594,   350,   296,   294,
    -197,   -91,  -309,   440,   331,   292,   549,    25,   284,   312,
     393,   393,  -196,   600,   601,   284,   284,   284,   284,   284,
     284,   284,   400,   546,  -197,   -91,   300,  -195,   284,   576,
     576,   301,   440,   440,   440,   440,   440,   588,   284,   764,
     -90,   765,   511,   651,   284,   517,   284,   284,   284,   320,
    -196,  -195,   517,   313,   517,    21,    22,   331,    69,    70,
    -198,    23,  -194,   549,   -90,   -92,   331,    21,    22,  -187,
     767,    70,   425,    23,  -196,   198,    30,   607,    33,   610,
     612,   614,   407,    31,  -198,   131,  -194,   132,   389,   -92,
     533,   533,   533,   533,   533,   785,   786,   533,   533,   544,
     441,   198,   384,   397,   321,   515,   515,   511,   421,   421,
     421,   421,   421,   421,   421,   256,   168,   319,   170,   517,
      25,   739,   517,   572,   333,   517,   517,   516,   516,   338,
      21,    22,    25,   589,    70,   256,    23,   421,   578,   341,
    -360,   340,   217,   530,   555,   256,   791,   229,   217,   230,
     117,   342,   118,   256,   256,   256,   699,   532,   365,   284,
     366,    21,    22,   637,    69,   707,    71,    23,  -361,   540,
     791,    21,    22,   364,   219,   517,   284,    23,   343,   782,
     304,   783,   502,  -264,  -264,   657,  -264,    21,    22,   334,
     367,   517,   529,    23,   376,    25,    24,   470,   383,   386,
     305,   222,   517,   387,   388,   412,   119,   414,   127,   503,
     698,  -264,   517,   413,   432,   753,   411,    21,    22,   168,
      69,   170,    71,    23,   120,   591,    25,   519,   149,   336,
     495,   433,   499,   515,   434,   443,    25,   444,   704,   445,
     515,   499,   515,   447,   647,   217,   126,   651,   292,   467,
     531,   217,    25,   542,   667,   516,   473,   479,   474,   475,
     476,   485,   516,   198,   516,   503,   256,   477,   446,   284,
     306,   679,   482,   284,    48,    48,   483,    71,    48,    48,
      48,    48,    25,   256,   588,   284,   393,   486,   500,    93,
     490,    93,   501,    21,    22,   163,   210,   276,    93,    23,
     -29,   -29,   -29,   -29,   149,    93,    93,   515,   -29,   520,
     515,    76,    30,   515,   515,    30,   527,   521,    77,    31,
     523,   545,    31,   526,   556,   217,   422,   217,   -29,   516,
     557,   441,   516,   558,   217,   516,   516,   748,   559,   284,
     284,   561,   564,    93,    93,    93,   210,   276,   602,   603,
      21,    22,   439,    69,    70,   615,    23,   617,    25,   618,
      93,   619,    93,   515,   733,   620,   721,   165,   738,   621,
     623,   284,   624,   626,   533,   627,   256,   629,   421,   515,
     256,    93,   628,   630,   119,   516,   127,   163,   805,   637,
     515,  -216,   638,   639,   423,   641,   346,   210,   416,   356,
     515,   516,   120,   640,   648,    49,   659,    30,    54,    55,
      56,    57,   516,   660,    31,    25,   171,   661,   662,    21,
      22,   663,   516,    70,   126,    23,   650,   664,   665,   670,
     429,    30,   150,   680,   770,   771,   356,   208,    31,   150,
     389,   681,   682,   683,   684,   685,   256,   256,   633,   -47,
     686,   346,   276,   700,   687,   533,    21,    22,    68,    69,
      70,    71,    23,    72,    73,    24,   667,   390,    21,    22,
     689,    69,   690,    71,    23,   688,   692,    74,   256,   693,
     706,   702,   439,   708,    25,   150,   647,   208,   711,   797,
     712,   204,   722,   729,   422,   422,   422,   422,   422,   422,
     422,   150,   723,   150,   371,   727,   730,   728,   574,   574,
     737,   439,   439,   439,   439,   439,   503,   731,   740,    93,
     741,    25,   150,   422,    93,    75,    93,   742,   743,    93,
      93,    93,    93,    25,   749,   752,   759,   761,   208,   206,
     208,   204,   -31,   -31,   -31,   -31,   760,    93,  -186,   762,
     -31,    93,    93,    93,   763,   768,  -130,  -130,  -130,  -130,
      93,    93,   423,   423,   423,   423,   423,   423,   423,   769,
     -31,   773,   774,   346,   346,   775,   705,   208,   -28,   -28,
     -28,   -28,   356,   713,  -130,   715,   -28,   776,   779,   206,
     781,   423,   204,   794,   204,   795,   796,   356,   356,   356,
     356,   356,   801,   356,   356,   356,   -28,   799,   356,  -131,
    -131,  -131,  -131,   804,   806,   707,   346,   356,   356,   356,
     346,   346,   309,   744,   732,   669,   780,  -113,   308,  -113,
    -113,   204,   380,   415,   745,   717,   645,  -131,   631,   778,
     206,   504,   206,   788,   673,   777,   323,   324,   325,   758,
     755,   326,   798,   756,   772,   416,   757,   766,    94,   754,
      94,   410,    21,    22,    94,   211,   701,    94,    23,   315,
     493,    24,   468,   346,    94,    94,   442,   724,   597,   206,
     746,   694,   327,   328,   417,   322,   808,   337,   150,   481,
     608,     0,   150,   150,   150,     0,     0,     0,   323,   324,
     325,   150,   150,   326,     0,     0,   715,     0,     0,     0,
     451,     0,    94,    94,    94,   211,   452,   453,     0,     0,
     454,   455,   790,   208,   456,     0,     0,   457,     0,    94,
       0,    94,     0,   633,   327,   328,   329,     0,   208,   208,
     208,   208,   208,   633,   208,  -133,  -133,  -133,  -133,   208,
      94,   356,     0,     0,     0,   356,    94,     0,   208,   208,
     208,     0,     0,     0,   422,   347,   211,     0,   211,     0,
     356,     0,     0,  -133,     0,     0,   356,   204,     0,     0,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
       0,     0,   204,   204,   204,   204,   204,     0,   204,     0,
       0,   288,     0,   204,     0,   211,     0,     0,     0,     0,
       0,     0,   204,   204,   204,   368,     0,     0,     0,     0,
     347,     0,     0,   673,     0,   206,     0,     0,   323,   324,
     325,     0,   423,   326,     0,     0,     0,     0,     0,     0,
     206,   206,   206,   206,   206,    25,   206,     0,     0,    93,
       0,   206,     0,     0,     0,    93,     0,     0,     0,     0,
     206,   206,   206,     0,   327,   328,   369,     5,     0,     0,
       6,     7,   346,   356,     8,     9,     0,    10,    11,   356,
       0,   356,     0,     0,    21,    22,     0,    69,    94,    71,
      23,     0,     0,    94,     0,    94,   346,   219,    94,    94,
      94,    94,     0,     0,     0,   787,     0,     0,     0,     0,
       0,   208,     0,     0,     0,     0,    94,   208,     0,     0,
      94,    94,    94,     0,   222,     0,     0,     0,     0,    94,
      94,    93,   503,    93,     0,     0,     0,     0,     0,     0,
       0,     0,   347,   347,     0,     0,     0,     0,     0,    25,
       0,   211,     0,   356,     0,   356,     0,     0,     0,   356,
       0,     0,   356,     0,     0,   204,   211,   211,   211,   211,
     211,   204,   211,   211,   211,     0,     0,   211,     0,     0,
       0,     0,     0,     0,     0,   347,   211,   211,   211,   347,
     347,   420,     0,   356,     0,     0,   150,     0,     0,     0,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
     128,     0,     0,   206,   208,     0,     0,   437,     0,   206,
     208,   316,     0,     0,     0,     0,     0,    97,     0,    97,
       0,     0,     0,   164,   214,   280,    97,     0,     0,   130,
       0,     0,   347,    97,    97,    21,    22,    68,    69,    70,
       0,    23,    72,    73,    24,     0,   218,     0,     0,     0,
       0,     0,   220,     0,     0,    25,   672,     0,   204,   133,
       0,     0,   150,     0,   204,     0,     0,     0,     0,     0,
       0,    97,    97,    97,   214,   280,   223,     0,     0,     0,
     226,   227,   228,   229,   208,   230,   208,     0,    97,     0,
      97,     0,     0,   208,     0,     0,     0,     0,     0,     0,
      25,   232,     0,     0,     0,     0,   206,     0,     0,    97,
     211,   650,   206,     0,   211,   164,     0,     0,     0,     0,
       0,     0,     0,     0,   348,   214,     0,   357,     0,   211,
     362,     0,     0,     0,     0,   211,     0,   437,   204,     0,
     204,     0,     0,     0,     0,     0,     0,   204,     0,   420,
     420,   420,   420,   420,   420,   420,     0,     0,     0,     0,
       0,     0,     0,     0,   357,     0,   579,   579,   579,   579,
     579,     0,     0,     0,     0,     0,     0,     0,   592,   348,
     280,     0,     0,     0,     0,     0,   206,     0,   206,     0,
       0,   362,     0,     0,     0,   206,    21,    22,    68,    69,
      70,    71,    23,    72,    73,    24,   128,     0,    94,     0,
       0,     0,     0,   165,    94,     0,     0,   166,   167,     0,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
       0,   347,   211,     0,     0,   130,     0,   165,   211,     0,
     211,   539,     0,     0,   168,   169,   170,    97,     0,     0,
       0,     0,    97,     0,    97,   347,     0,    97,    97,    97,
      97,    25,   171,   172,     0,   133,     0,     0,   168,   173,
     170,     0,   174,     0,     0,    97,     0,     0,     0,    97,
      97,    97,     0,     0,     0,    25,   171,     0,    97,    97,
      94,     0,    94,     0,     0,     0,     0,     0,     0,     0,
       0,   348,   348,     0,     0,     0,     0,     0,     0,     0,
     357,     0,   211,     0,   211,     0,     0,     0,   211,     0,
       0,   211,     0,     0,     0,   357,   357,   357,   357,   357,
       0,   357,   357,   357,     0,     0,   357,     0,     0,     0,
       0,     0,     0,     0,   348,   357,   357,   357,   348,   348,
       0,     0,   211,     0,     0,     0,    21,    22,    68,    69,
      70,    71,    23,    72,    73,    24,     0,     0,    21,    22,
      68,    69,    70,    71,    23,    72,    73,    24,   128,   218,
       0,   219,     0,     0,     0,   220,    98,     0,    98,   435,
       0,     0,    98,   215,     0,    98,     0,     0,     0,     0,
       0,   348,    98,    98,     0,     0,     0,   130,   222,   223,
       0,   224,   225,   226,   227,   228,   229,     0,   230,   592,
     231,    25,     0,     0,     0,    75,     0,     0,     0,     0,
       0,     0,     0,    25,   232,     0,     0,     0,     0,     0,
      98,    98,    98,   215,   174,     0,    21,    22,    68,    69,
      70,    71,    23,    72,    73,    24,   155,    98,     0,    98,
       0,     0,     0,     0,     0,     0,     0,   156,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    98,     0,
       0,     0,     0,   357,    98,     0,     0,     0,     0,     0,
       0,     0,     0,   349,   215,     0,   215,     0,   357,   349,
      95,     0,    95,     0,   357,     0,    95,   212,     0,    95,
       0,    25,     0,     0,     0,    75,    95,    95,     0,     0,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
     128,     0,     0,   215,     0,     0,     0,   165,     0,     0,
       0,   351,   167,     0,     0,     0,     0,     0,   349,     0,
       0,     0,     0,     0,    95,    95,    95,   212,     0,   130,
     349,     0,     0,     0,     0,     0,     0,     0,   168,   169,
     170,    95,     0,    95,     0,     0,     0,    97,     0,     0,
       0,     0,     0,    97,     0,    25,   171,   172,     0,   133,
       0,     0,    95,   173,     0,     0,   174,     0,    95,     0,
     348,   357,     0,     0,     0,     0,     0,   357,   212,   357,
     212,     0,     0,   360,     0,     0,    98,     0,     0,     0,
       0,    98,     0,    98,   348,     0,    98,    98,    98,    98,
       0,     0,     0,     0,    21,    22,    68,    69,    70,    71,
      23,    72,    73,    24,    98,     0,     0,   212,    98,    98,
      98,     0,     0,     0,     0,   156,     0,    98,    98,    97,
       0,    97,     0,     0,     0,     0,     0,     0,     0,     0,
     349,   349,     0,     0,   360,     0,     0,     0,     0,   215,
       0,   357,     0,   357,     0,     0,     0,   357,     0,     0,
     357,     0,     0,     0,   215,   215,   215,   215,   215,    25,
     215,   215,   215,    75,     0,   215,     0,     0,     0,     0,
       0,     0,     0,   349,   215,   215,   215,   349,   349,     0,
      21,    22,    68,    69,    70,    71,    23,    72,    73,    24,
      95,     0,     0,     0,     0,    95,     0,    95,     0,     0,
      95,    95,    95,    95,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    95,     0,
       0,     0,    95,    95,    95,     0,     0,     0,     0,     0,
     349,    95,    95,     0,    21,    22,     0,    69,    70,    71,
      23,     0,     0,     0,   128,    25,     0,     0,     0,     0,
       0,   165,     0,   212,     0,   377,   167,    21,    22,    68,
      69,    70,    71,    23,    72,    73,    24,   155,   212,   212,
     212,   212,   212,   130,   212,   212,   212,     0,    74,   212,
       0,     0,     0,   169,     0,     0,     0,   550,   212,   212,
     212,     0,     0,     0,     0,     0,     0,     0,     0,    25,
     171,   172,     0,   133,     0,     0,     0,   173,     0,     0,
     174,     0,   215,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    25,     0,     0,     0,    75,   215,     0,    96,
       0,    96,     0,   215,     0,    96,   213,     0,    96,     0,
       0,     0,     0,     0,   550,    96,    96,     0,     0,    21,
      22,    68,    69,    70,    71,    23,    72,    73,    24,   128,
     218,     0,   219,     0,     0,     0,   220,     0,     0,     0,
     221,   167,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    96,    96,    96,   213,     0,   130,   222,
     223,     0,   224,   225,   226,   227,   228,   229,   169,   230,
      96,   231,    96,     0,     0,     0,    98,     0,     0,     0,
       0,     0,    98,     0,    25,   232,   172,     0,   133,     0,
       0,    96,   173,     0,     0,   174,   212,    96,     0,   349,
     215,     0,     0,     0,     0,     0,   215,   213,   215,   213,
       0,   212,   361,     0,     0,     0,     0,   212,     0,     0,
       0,     0,     0,   349,     0,     0,     0,     0,    21,    22,
      68,    69,    70,    71,    23,    72,    73,    24,   128,     0,
       0,     0,     0,     0,     0,   100,   213,   100,     0,   129,
       0,   100,   216,     0,   100,     0,     0,     0,    98,     0,
      98,   100,   100,     0,     0,     0,     0,   130,     0,     0,
       0,     0,     0,   361,     0,     0,   131,     0,   132,     0,
     215,     0,   215,     0,     0,     0,   215,     0,     0,   215,
      95,     0,     0,    25,     0,     0,    95,   133,     0,   100,
     100,   100,   216,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   212,     0,   100,     0,   100,     0,
     212,     0,   212,   291,     0,     0,     0,     0,     0,    96,
       0,   394,     0,   167,    96,     0,    96,   100,     0,    96,
      96,    96,    96,   100,   323,   324,   325,   292,     0,   326,
       0,     0,     0,   216,     0,   358,     0,    96,     0,     0,
     169,    96,    96,    96,     0,     0,     0,     0,     0,     0,
      96,    96,    95,     0,    95,     0,     0,     0,   172,     0,
     395,   328,   396,     0,   173,     0,     0,     0,     0,     0,
       0,     0,   213,     0,   212,     0,   212,     0,     0,     0,
     212,     0,     0,   212,     0,     0,     0,   213,   213,   213,
     213,   213,     0,   213,   213,   213,     0,     0,   213,     0,
       0,     0,     0,     0,     0,     0,   361,   213,   213,   213,
       0,    21,    22,    68,    69,    70,    71,    23,    72,    73,
      24,     0,   218,     0,     0,     0,     0,     0,   220,     0,
       0,     0,   573,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   223,     0,     0,   100,   226,   227,   228,   229,
     100,   230,   100,   361,     0,   100,   100,   100,   100,     0,
       0,     0,     0,     0,     0,     0,    25,   232,     0,     0,
       0,     0,     0,   100,     0,     0,     0,   100,   100,   100,
       0,     0,     0,     0,     0,     0,   100,   100,    21,    22,
      68,     0,     0,    71,    23,    72,    73,    24,     0,     0,
       0,     0,   112,   113,   114,     0,   115,   116,   216,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   216,   216,   216,   216,   216,     0,   358,
     216,   216,     0,     0,   216,   213,   117,     0,   118,     0,
       0,     0,     0,   358,   358,   358,     0,     0,     0,     0,
     213,     0,     0,    25,     0,     0,   213,    21,    22,    68,
      69,    70,    71,    23,    72,    73,    24,   128,   218,   291,
     219,     0,     0,     0,   220,     0,     0,   394,   221,   167,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     323,   324,   325,   292,     0,   326,   130,   222,   223,     0,
     224,   225,   226,   227,   228,   229,   169,   230,     0,   231,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    25,   232,   172,     0,   395,   328,   396,    96,
     173,     0,     0,   174,     0,    96,     0,     0,     0,     0,
       0,    21,    22,    68,    69,    70,    71,    23,    72,    73,
      24,   128,   218,   213,   219,     0,     0,     0,   220,   213,
       0,   213,   405,   167,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     130,   222,   223,     0,   224,   225,   226,   227,   228,   229,
     169,   230,     0,   231,     0,     0,   216,     0,     0,     0,
       0,     0,   358,     0,     0,     0,    25,   232,   172,     0,
     133,    96,     0,    96,   173,     0,     0,   174,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   213,     0,   213,     0,     0,     0,   213,
       0,     0,   213,     0,    21,    22,    68,    69,    70,    71,
      23,    72,    73,    24,   128,   218,   291,   219,     0,     0,
       0,   220,     0,     0,   394,   405,   167,     0,     0,     0,
       0,     0,     0,     0,     0,   100,     0,   323,   324,   325,
     292,   100,   326,   130,   222,   223,     0,   224,   225,   226,
     227,   228,   229,   169,   230,     0,   231,     0,     0,   358,
       0,     0,     0,     0,     0,   358,     0,   216,     0,    25,
     232,   172,     0,   395,   328,   396,     0,   173,     0,     0,
     174,     0,     0,     0,    21,    22,    68,    69,    70,    71,
      23,    72,    73,    24,   128,   218,     0,   219,     0,     0,
       0,   220,     0,     0,     0,   435,   167,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   100,     0,   100,
       0,     0,     0,   130,   222,   223,     0,   224,   225,   226,
     227,   228,   229,   169,   230,     0,   231,     0,     0,   358,
       0,   358,     0,     0,     0,     0,     0,     0,   216,    25,
     232,   172,     0,   133,     0,     0,     0,   173,     0,     0,
     174,    21,    22,    68,    69,    70,    71,    23,    72,    73,
      24,   128,   218,     0,   219,     0,     0,     0,   220,     0,
       0,     0,   405,   167,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     130,   222,   223,     0,   224,   225,   226,   227,   228,   666,
     169,   230,     0,   231,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    25,   232,   172,     0,
     133,     0,     0,     0,   173,     0,     0,   174
};

static const yytype_int16 yycheck[] =
{
       5,     6,     7,     8,     9,    10,    11,     5,     6,   150,
       8,     9,    10,    11,    59,   229,    59,   248,    59,   524,
      64,    65,     5,     6,    75,     8,     9,    10,    11,   562,
     296,   129,    59,   131,    60,   150,   205,    58,    65,    66,
     221,    67,   341,    64,    58,    50,   114,   300,   301,   150,
      64,   520,    50,    74,    59,   562,    65,    66,    63,   372,
      74,    75,   502,   114,   441,    63,   114,    50,    88,   220,
     221,   115,   117,    24,   117,   366,   367,   368,   369,   370,
      63,    65,   148,   270,   429,   373,   374,   113,   115,   116,
     117,   112,    67,   143,   205,   197,   441,   615,   112,     9,
      33,    51,    35,   129,    26,   131,   115,   116,    75,   383,
      77,    78,   117,   429,   430,   431,   432,   433,     6,     7,
      71,   165,     3,     4,   150,   441,   341,    77,     9,    24,
       0,   115,   182,    29,    66,   156,   114,    29,   113,   166,
      29,   168,   156,   386,   387,   388,    66,   152,   366,   367,
     368,   369,   370,   255,   152,    77,    29,   244,    68,    65,
      29,    15,   366,   367,   368,   369,   370,    88,    15,   152,
      51,   689,    53,   642,   692,   693,    71,   197,   205,   320,
     321,   322,   166,    29,   116,    39,    40,    68,   329,   330,
     256,   241,    39,    40,   221,    29,   116,   366,   367,   368,
     369,   370,   229,   502,   503,   320,   321,   322,   741,   115,
      27,   220,   221,   400,   329,   330,    15,   244,   316,   320,
     321,   322,    29,   728,   405,   293,    30,   295,   329,   330,
      54,   299,   300,   301,   741,   255,    74,   288,   389,   390,
      39,    29,   293,   270,   295,   293,    29,   295,   299,   300,
     301,   299,   300,   301,   435,   366,   367,   368,   369,   370,
     166,    29,   373,   374,    33,    58,    35,   312,   313,   312,
     313,   312,    26,    27,   288,    29,   197,   298,    33,   689,
      35,    74,   692,   693,   298,   312,   313,   502,   503,   221,
     316,   296,    29,   762,   320,   321,   322,    29,   296,   343,
      54,   221,   545,   329,   330,   682,   333,   312,   313,   229,
     244,   338,     3,     4,   341,   293,     7,   295,     9,   112,
      15,   299,   300,   301,   351,   412,   413,   414,   415,   416,
     417,   418,    29,    24,   255,   648,   341,   682,    24,   366,
     367,   368,   369,   370,    39,   372,   373,   374,    15,    29,
     377,    15,   426,   427,   441,   629,   383,   797,    15,   386,
     387,   388,   650,   156,   638,   618,   682,   351,    29,   290,
      15,    15,    39,   400,    31,    39,   385,    68,   405,    33,
     389,   390,    39,   444,   445,   412,   413,   414,   415,   416,
     417,   418,   573,   377,    39,    39,    24,    15,   425,   426,
     427,    24,   429,   430,   431,   432,   433,   434,   435,   722,
      15,   724,   711,   524,   441,   630,   443,   444,   445,    74,
      15,    39,   637,    24,   639,     3,     4,    31,     6,     7,
      15,     9,    15,   442,    39,    15,    31,     3,     4,    34,
     731,     7,   673,     9,    39,   351,   451,   452,   453,   454,
     455,   456,   666,   451,    39,    51,    39,    53,    24,    39,
     366,   367,   368,   369,   370,   774,   775,   373,   374,   375,
      33,   377,    35,   405,    23,   502,   503,   776,   412,   413,
     414,   415,   416,   417,   418,   405,    51,   134,    53,   704,
      68,   672,   707,   425,    51,   710,   711,   502,   503,    51,
       3,     4,    68,   435,     7,   425,     9,   441,   428,    33,
      33,   158,   539,   731,   665,   435,   782,    51,   545,    53,
      51,    24,    53,   443,   444,   445,   624,   731,   175,   556,
      74,     3,     4,    75,     6,    77,     8,     9,    33,   650,
     806,     3,     4,    32,    16,   760,   573,     9,    51,    51,
     618,    53,    24,    26,    27,   539,    29,     3,     4,   700,
      23,   776,   731,     9,    45,    68,    12,   618,    51,    24,
     618,    43,   787,    24,    24,    74,   621,    45,   621,    51,
     621,    54,   797,    23,    77,   700,   233,     3,     4,    51,
       6,    53,     8,     9,   621,   682,    68,   641,   624,   700,
     627,    78,   629,   630,    51,    24,    68,    24,    24,    24,
     637,   638,   639,    26,   520,   642,   621,   728,    39,    27,
     731,   648,    68,   650,   556,   630,    26,    54,    26,    26,
      26,    54,   637,   539,   639,    51,   556,    26,   285,   666,
     618,   573,    26,   670,    39,    40,    26,     8,    43,    44,
      45,    46,    68,   573,   681,   682,   665,    27,    26,    58,
      74,    60,    27,     3,     4,    64,    65,    66,    67,     9,
      26,    27,    28,    29,   700,    74,    75,   704,    34,    29,
     707,   702,   687,   710,   711,   690,    27,    26,   702,   687,
      54,    24,   690,    75,    29,   722,   244,   724,    54,   704,
      26,    33,   707,    26,   731,   710,   711,   690,    26,   736,
     737,    54,    27,   112,   113,   114,   115,   116,    27,    26,
       3,     4,   270,     6,     7,    29,     9,    26,    68,    29,
     129,    26,   131,   760,   666,    26,   642,    20,   670,    29,
      26,   768,    29,    54,   650,    29,   666,    29,   682,   776,
     670,   150,    54,    33,   799,   760,   799,   156,   799,    75,
     787,    75,    51,    24,   244,    29,   165,   166,    45,   168,
     797,   776,   799,    54,    29,    40,    26,   782,    43,    44,
      45,    46,   787,    54,   782,    68,    69,    26,    26,     3,
       4,    26,   797,     7,   799,     9,    79,    54,    29,    29,
      75,   806,    60,    54,   736,   737,   205,    65,   806,    67,
      24,    29,    33,    26,    26,    26,   736,   737,   502,    45,
      26,   220,   221,    33,    29,   731,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,   768,    51,     3,     4,
      29,     6,    29,     8,     9,    54,    29,    24,   768,    29,
      26,    33,   400,    26,    68,   113,   762,   115,    29,    24,
      54,    65,    29,    26,   412,   413,   414,   415,   416,   417,
     418,   129,    34,   131,    40,    28,    26,    29,   426,   427,
      29,   429,   430,   431,   432,   433,    51,    33,    28,   288,
      29,    68,   150,   441,   293,    72,   295,    26,    33,   298,
     299,   300,   301,    68,    26,    26,    54,    26,   166,    65,
     168,   115,    26,    27,    28,    29,    29,   316,    34,    29,
      34,   320,   321,   322,    54,    29,    26,    27,    28,    29,
     329,   330,   412,   413,   414,   415,   416,   417,   418,    54,
      54,    29,    29,   342,   343,    29,   630,   205,    26,    27,
      28,    29,   351,   637,    54,   639,    34,    33,    26,   115,
      26,   441,   166,    26,   168,    26,    26,   366,   367,   368,
     369,   370,    54,   372,   373,   374,    54,    33,   377,    26,
      27,    28,    29,    26,    29,    77,   385,   386,   387,   388,
     389,   390,   116,   681,   665,   556,   768,    75,   115,    77,
      78,   205,   205,    23,   682,   641,   520,    54,   502,   762,
     166,   341,   168,   776,   562,   760,    36,    37,    38,   711,
     704,    41,   787,   707,   741,    45,   710,   728,    58,   702,
      60,   232,     3,     4,    64,    65,   627,    67,     9,   129,
     332,    12,   298,   442,    74,    75,   275,   646,   442,   205,
     687,   613,    72,    73,    74,    23,   806,   152,   316,   313,
     453,    -1,   320,   321,   322,    -1,    -1,    -1,    36,    37,
      38,   329,   330,    41,    -1,    -1,   760,    -1,    -1,    -1,
      51,    -1,   112,   113,   114,   115,    57,    58,    -1,    -1,
      61,    62,   776,   351,    65,    -1,    -1,    68,    -1,   129,
      -1,   131,    -1,   787,    72,    73,    74,    -1,   366,   367,
     368,   369,   370,   797,   372,    26,    27,    28,    29,   377,
     150,   520,    -1,    -1,    -1,   524,   156,    -1,   386,   387,
     388,    -1,    -1,    -1,   682,   165,   166,    -1,   168,    -1,
     539,    -1,    -1,    54,    -1,    -1,   545,   351,    -1,    -1,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      -1,    -1,   366,   367,   368,   369,   370,    -1,   372,    -1,
      -1,    24,    -1,   377,    -1,   205,    -1,    -1,    -1,    -1,
      -1,    -1,   386,   387,   388,    23,    -1,    -1,    -1,    -1,
     220,    -1,    -1,   741,    -1,   351,    -1,    -1,    36,    37,
      38,    -1,   682,    41,    -1,    -1,    -1,    -1,    -1,    -1,
     366,   367,   368,   369,   370,    68,   372,    -1,    -1,   618,
      -1,   377,    -1,    -1,    -1,   624,    -1,    -1,    -1,    -1,
     386,   387,   388,    -1,    72,    73,    74,    56,    -1,    -1,
      59,    60,   641,   642,    63,    64,    -1,    66,    67,   648,
      -1,   650,    -1,    -1,     3,     4,    -1,     6,   288,     8,
       9,    -1,    -1,   293,    -1,   295,   665,    16,   298,   299,
     300,   301,    -1,    -1,    -1,    24,    -1,    -1,    -1,    -1,
      -1,   539,    -1,    -1,    -1,    -1,   316,   545,    -1,    -1,
     320,   321,   322,    -1,    43,    -1,    -1,    -1,    -1,   329,
     330,   700,    51,   702,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   342,   343,    -1,    -1,    -1,    -1,    -1,    68,
      -1,   351,    -1,   722,    -1,   724,    -1,    -1,    -1,   728,
      -1,    -1,   731,    -1,    -1,   539,   366,   367,   368,   369,
     370,   545,   372,   373,   374,    -1,    -1,   377,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   385,   386,   387,   388,   389,
     390,   244,    -1,   762,    -1,    -1,   624,    -1,    -1,    -1,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    -1,    -1,   539,   642,    -1,    -1,   270,    -1,   545,
     648,    24,    -1,    -1,    -1,    -1,    -1,    58,    -1,    60,
      -1,    -1,    -1,    64,    65,    66,    67,    -1,    -1,    42,
      -1,    -1,   442,    74,    75,     3,     4,     5,     6,     7,
      -1,     9,    10,    11,    12,    -1,    14,    -1,    -1,    -1,
      -1,    -1,    20,    -1,    -1,    68,    24,    -1,   642,    72,
      -1,    -1,   700,    -1,   648,    -1,    -1,    -1,    -1,    -1,
      -1,   112,   113,   114,   115,   116,    44,    -1,    -1,    -1,
      48,    49,    50,    51,   722,    53,   724,    -1,   129,    -1,
     131,    -1,    -1,   731,    -1,    -1,    -1,    -1,    -1,    -1,
      68,    69,    -1,    -1,    -1,    -1,   642,    -1,    -1,   150,
     520,    79,   648,    -1,   524,   156,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   165,   166,    -1,   168,    -1,   539,
     171,    -1,    -1,    -1,    -1,   545,    -1,   400,   722,    -1,
     724,    -1,    -1,    -1,    -1,    -1,    -1,   731,    -1,   412,
     413,   414,   415,   416,   417,   418,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   205,    -1,   429,   430,   431,   432,
     433,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   441,   220,
     221,    -1,    -1,    -1,    -1,    -1,   722,    -1,   724,    -1,
      -1,   232,    -1,    -1,    -1,   731,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    13,    -1,   618,    -1,
      -1,    -1,    -1,    20,   624,    -1,    -1,    24,    25,    -1,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      -1,   641,   642,    -1,    -1,    42,    -1,    20,   648,    -1,
     650,    24,    -1,    -1,    51,    52,    53,   288,    -1,    -1,
      -1,    -1,   293,    -1,   295,   665,    -1,   298,   299,   300,
     301,    68,    69,    70,    -1,    72,    -1,    -1,    51,    76,
      53,    -1,    79,    -1,    -1,   316,    -1,    -1,    -1,   320,
     321,   322,    -1,    -1,    -1,    68,    69,    -1,   329,   330,
     700,    -1,   702,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   342,   343,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     351,    -1,   722,    -1,   724,    -1,    -1,    -1,   728,    -1,
      -1,   731,    -1,    -1,    -1,   366,   367,   368,   369,   370,
      -1,   372,   373,   374,    -1,    -1,   377,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   385,   386,   387,   388,   389,   390,
      -1,    -1,   762,    -1,    -1,    -1,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    -1,    -1,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      -1,    16,    -1,    -1,    -1,    20,    58,    -1,    60,    24,
      -1,    -1,    64,    65,    -1,    67,    -1,    -1,    -1,    -1,
      -1,   442,    74,    75,    -1,    -1,    -1,    42,    43,    44,
      -1,    46,    47,    48,    49,    50,    51,    -1,    53,   682,
      55,    68,    -1,    -1,    -1,    72,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    68,    69,    -1,    -1,    -1,    -1,    -1,
     112,   113,   114,   115,    79,    -1,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    13,   129,    -1,   131,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    24,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   150,    -1,
      -1,    -1,    -1,   524,   156,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   165,   166,    -1,   168,    -1,   539,   171,
      58,    -1,    60,    -1,   545,    -1,    64,    65,    -1,    67,
      -1,    68,    -1,    -1,    -1,    72,    74,    75,    -1,    -1,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    -1,    -1,   205,    -1,    -1,    -1,    20,    -1,    -1,
      -1,    24,    25,    -1,    -1,    -1,    -1,    -1,   220,    -1,
      -1,    -1,    -1,    -1,   112,   113,   114,   115,    -1,    42,
     232,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    51,    52,
      53,   129,    -1,   131,    -1,    -1,    -1,   618,    -1,    -1,
      -1,    -1,    -1,   624,    -1,    68,    69,    70,    -1,    72,
      -1,    -1,   150,    76,    -1,    -1,    79,    -1,   156,    -1,
     641,   642,    -1,    -1,    -1,    -1,    -1,   648,   166,   650,
     168,    -1,    -1,   171,    -1,    -1,   288,    -1,    -1,    -1,
      -1,   293,    -1,   295,   665,    -1,   298,   299,   300,   301,
      -1,    -1,    -1,    -1,     3,     4,     5,     6,     7,     8,
       9,    10,    11,    12,   316,    -1,    -1,   205,   320,   321,
     322,    -1,    -1,    -1,    -1,    24,    -1,   329,   330,   700,
      -1,   702,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     342,   343,    -1,    -1,   232,    -1,    -1,    -1,    -1,   351,
      -1,   722,    -1,   724,    -1,    -1,    -1,   728,    -1,    -1,
     731,    -1,    -1,    -1,   366,   367,   368,   369,   370,    68,
     372,   373,   374,    72,    -1,   377,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   385,   386,   387,   388,   389,   390,    -1,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
     288,    -1,    -1,    -1,    -1,   293,    -1,   295,    -1,    -1,
     298,   299,   300,   301,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   316,    -1,
      -1,    -1,   320,   321,   322,    -1,    -1,    -1,    -1,    -1,
     442,   329,   330,    -1,     3,     4,    -1,     6,     7,     8,
       9,    -1,    -1,    -1,    13,    68,    -1,    -1,    -1,    -1,
      -1,    20,    -1,   351,    -1,    24,    25,     3,     4,     5,
       6,     7,     8,     9,    10,    11,    12,    13,   366,   367,
     368,   369,   370,    42,   372,   373,   374,    -1,    24,   377,
      -1,    -1,    -1,    52,    -1,    -1,    -1,   385,   386,   387,
     388,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    68,
      69,    70,    -1,    72,    -1,    -1,    -1,    76,    -1,    -1,
      79,    -1,   524,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    68,    -1,    -1,    -1,    72,   539,    -1,    58,
      -1,    60,    -1,   545,    -1,    64,    65,    -1,    67,    -1,
      -1,    -1,    -1,    -1,   442,    74,    75,    -1,    -1,     3,
       4,     5,     6,     7,     8,     9,    10,    11,    12,    13,
      14,    -1,    16,    -1,    -1,    -1,    20,    -1,    -1,    -1,
      24,    25,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   112,   113,   114,   115,    -1,    42,    43,
      44,    -1,    46,    47,    48,    49,    50,    51,    52,    53,
     129,    55,   131,    -1,    -1,    -1,   618,    -1,    -1,    -1,
      -1,    -1,   624,    -1,    68,    69,    70,    -1,    72,    -1,
      -1,   150,    76,    -1,    -1,    79,   524,   156,    -1,   641,
     642,    -1,    -1,    -1,    -1,    -1,   648,   166,   650,   168,
      -1,   539,   171,    -1,    -1,    -1,    -1,   545,    -1,    -1,
      -1,    -1,    -1,   665,    -1,    -1,    -1,    -1,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    -1,
      -1,    -1,    -1,    -1,    -1,    58,   205,    60,    -1,    24,
      -1,    64,    65,    -1,    67,    -1,    -1,    -1,   700,    -1,
     702,    74,    75,    -1,    -1,    -1,    -1,    42,    -1,    -1,
      -1,    -1,    -1,   232,    -1,    -1,    51,    -1,    53,    -1,
     722,    -1,   724,    -1,    -1,    -1,   728,    -1,    -1,   731,
     618,    -1,    -1,    68,    -1,    -1,   624,    72,    -1,   112,
     113,   114,   115,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   642,    -1,   129,    -1,   131,    -1,
     648,    -1,   650,    15,    -1,    -1,    -1,    -1,    -1,   288,
      -1,    23,    -1,    25,   293,    -1,   295,   150,    -1,   298,
     299,   300,   301,   156,    36,    37,    38,    39,    -1,    41,
      -1,    -1,    -1,   166,    -1,   168,    -1,   316,    -1,    -1,
      52,   320,   321,   322,    -1,    -1,    -1,    -1,    -1,    -1,
     329,   330,   700,    -1,   702,    -1,    -1,    -1,    70,    -1,
      72,    73,    74,    -1,    76,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   351,    -1,   722,    -1,   724,    -1,    -1,    -1,
     728,    -1,    -1,   731,    -1,    -1,    -1,   366,   367,   368,
     369,   370,    -1,   372,   373,   374,    -1,    -1,   377,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   385,   386,   387,   388,
      -1,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    -1,    14,    -1,    -1,    -1,    -1,    -1,    20,    -1,
      -1,    -1,    24,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    44,    -1,    -1,   288,    48,    49,    50,    51,
     293,    53,   295,   442,    -1,   298,   299,   300,   301,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    68,    69,    -1,    -1,
      -1,    -1,    -1,   316,    -1,    -1,    -1,   320,   321,   322,
      -1,    -1,    -1,    -1,    -1,    -1,   329,   330,     3,     4,
       5,    -1,    -1,     8,     9,    10,    11,    12,    -1,    -1,
      -1,    -1,    17,    18,    19,    -1,    21,    22,   351,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   366,   367,   368,   369,   370,    -1,   372,
     373,   374,    -1,    -1,   377,   524,    51,    -1,    53,    -1,
      -1,    -1,    -1,   386,   387,   388,    -1,    -1,    -1,    -1,
     539,    -1,    -1,    68,    -1,    -1,   545,     3,     4,     5,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    -1,    -1,    -1,    20,    -1,    -1,    23,    24,    25,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      36,    37,    38,    39,    -1,    41,    42,    43,    44,    -1,
      46,    47,    48,    49,    50,    51,    52,    53,    -1,    55,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    68,    69,    70,    -1,    72,    73,    74,   618,
      76,    -1,    -1,    79,    -1,   624,    -1,    -1,    -1,    -1,
      -1,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,   642,    16,    -1,    -1,    -1,    20,   648,
      -1,   650,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      42,    43,    44,    -1,    46,    47,    48,    49,    50,    51,
      52,    53,    -1,    55,    -1,    -1,   539,    -1,    -1,    -1,
      -1,    -1,   545,    -1,    -1,    -1,    68,    69,    70,    -1,
      72,   700,    -1,   702,    76,    -1,    -1,    79,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   722,    -1,   724,    -1,    -1,    -1,   728,
      -1,    -1,   731,    -1,     3,     4,     5,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    15,    16,    -1,    -1,
      -1,    20,    -1,    -1,    23,    24,    25,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   618,    -1,    36,    37,    38,
      39,   624,    41,    42,    43,    44,    -1,    46,    47,    48,
      49,    50,    51,    52,    53,    -1,    55,    -1,    -1,   642,
      -1,    -1,    -1,    -1,    -1,   648,    -1,   650,    -1,    68,
      69,    70,    -1,    72,    73,    74,    -1,    76,    -1,    -1,
      79,    -1,    -1,    -1,     3,     4,     5,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    -1,    16,    -1,    -1,
      -1,    20,    -1,    -1,    -1,    24,    25,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   700,    -1,   702,
      -1,    -1,    -1,    42,    43,    44,    -1,    46,    47,    48,
      49,    50,    51,    52,    53,    -1,    55,    -1,    -1,   722,
      -1,   724,    -1,    -1,    -1,    -1,    -1,    -1,   731,    68,
      69,    70,    -1,    72,    -1,    -1,    -1,    76,    -1,    -1,
      79,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    -1,    16,    -1,    -1,    -1,    20,    -1,
      -1,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
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
      20,    24,    43,    44,    46,    47,    48,    49,    50,    51,
      53,    55,    69,    95,    96,    97,    98,    99,   100,   101,
     102,   103,   105,   106,   107,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   125,   127,   128,   133,   135,
     137,   138,   139,   140,   141,   142,   143,   197,   207,   246,
     247,   248,   249,   252,   256,   264,   268,   269,   270,   271,
     272,   273,   275,   277,   279,    87,   211,   243,    24,   224,
     236,    15,    39,   265,   266,   267,    29,    93,    74,    24,
      24,    24,   243,   211,   230,   233,   234,   236,   144,    95,
     307,   312,    33,    24,   212,   238,    24,   212,   240,    93,
      74,    23,    23,    36,    37,    38,    41,    72,    73,    74,
     254,    31,   257,    51,   218,   220,   221,   305,    51,   182,
      93,    33,    24,    51,   169,   182,   268,   269,   272,   273,
     145,    24,   145,   176,   178,   179,   268,   272,   277,   205,
     270,   271,   272,   274,    32,    93,    74,    23,    23,    74,
     254,    40,   259,   265,   267,   257,    45,    24,   152,   153,
     160,   162,   279,    51,    35,   250,    24,    24,    24,    24,
      51,   120,   133,   264,    23,    72,    74,    96,   126,   133,
     247,   254,   255,   266,   267,    24,    96,   130,   268,   272,
     205,    93,    74,    23,    45,    23,    45,    74,   254,   103,
     105,   110,   113,   117,   127,   259,   265,   267,   257,    75,
      77,    78,    77,    78,    51,    24,   104,   105,   111,   113,
     279,    33,   250,    24,    24,    24,    93,    26,   224,   236,
     236,    51,    57,    58,    61,    62,    65,    68,   280,   282,
     283,   285,   287,   288,   290,   292,   315,    27,   245,   235,
     236,   235,   235,    26,    26,    26,    26,    26,   313,    54,
     307,   312,    26,    26,   241,    54,    27,   220,   220,   220,
      74,   220,   220,   239,   223,   279,   156,   157,   158,   279,
      26,    27,    24,    51,   183,   184,   185,   187,   188,   190,
     192,   249,   260,   261,   262,   279,   319,   322,   170,   182,
      29,    26,   180,    54,    24,    71,    75,    27,   151,   153,
     159,   162,   166,   178,   151,   151,   151,   151,   176,    24,
     162,   177,   279,   177,   178,    24,   145,   156,   263,   264,
     270,   179,   179,   179,   121,   133,    29,    26,    26,    26,
     131,    54,    24,    71,    27,   103,   103,   103,   103,   103,
     103,   103,    96,    24,   113,   125,   279,   125,   127,   105,
     135,   138,   135,   135,   135,   135,   108,   109,   279,    96,
     102,   103,   105,   134,   135,   136,   138,   263,   129,   130,
     129,   129,    27,    26,   280,   281,   293,   319,   328,   284,
     319,   286,   319,   291,   319,    29,   300,    26,    29,    26,
      26,    29,   314,    26,    29,   242,    54,    29,    54,    29,
      33,   184,   187,   188,   191,   183,   193,    75,    51,    24,
      54,    29,    51,   163,   171,   172,   173,   178,    29,   181,
      79,   162,   195,   202,   203,   204,   206,   145,   179,    26,
      54,    26,    26,    26,    54,    29,    51,    96,   122,   123,
      29,   132,    24,   113,   142,   198,   199,   200,   206,    96,
      54,    29,    33,    26,    26,    26,    26,    29,    54,    29,
      29,   289,    29,    29,   300,   301,   311,   235,   307,   212,
      33,   223,    33,   156,    24,   188,    26,    77,    26,    26,
      77,    29,    54,   188,   156,   188,   189,   170,   163,   172,
     174,   178,    29,    34,   258,   176,   177,    28,    29,    26,
      26,    33,   121,    96,   123,   124,   258,    29,    96,   247,
      28,    29,    26,    33,   108,   134,   281,   301,   315,    26,
     301,   301,    26,   220,   209,   188,   188,   188,   193,    54,
      29,    26,    29,    54,   176,   176,   202,   151,    29,    54,
      96,    96,   198,    29,    29,    29,    33,   189,   174,    26,
     124,    26,    51,    53,   294,   294,   294,    24,   185,   186,
     188,   280,   295,   298,    26,    26,    26,    24,   190,    33,
     299,    54,   296,   187,    26,   307,    29,   297,   298
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int16 yyr1[] =
{
       0,    80,    81,    82,    83,    83,    84,    84,    85,    85,
      85,    85,    85,    85,    86,    87,    88,    89,    90,    91,
      92,    93,    93,    94,    94,    95,    95,    95,    96,    96,
      96,    96,    96,    96,    97,    97,    97,    98,    99,    99,
      99,   100,   100,   101,   101,   102,   102,   103,   103,   103,
     104,   104,   105,   105,   105,   105,   106,   107,   108,   108,
     109,   110,   110,   111,   112,   113,   113,   113,   113,   114,
     114,   115,   115,   115,   115,   115,   116,   116,   117,   118,
     119,   120,   120,   121,   121,   122,   122,   123,   124,   124,
     125,   125,   125,   126,   126,   126,   126,   126,   127,   127,
     128,   128,   128,   129,   130,   131,   131,   132,   133,   133,
     134,   134,   134,   135,   136,   137,   137,   137,   138,   138,
     139,   139,   140,   140,   141,   142,   143,   144,   144,   144,
     145,   145,   145,   145,   145,   145,   146,   146,   147,   148,
     148,   149,   149,   150,   150,   151,   151,   151,   152,   152,
     153,   153,   153,   153,   154,   155,   156,   156,   157,   157,
     158,   159,   159,   160,   161,   162,   162,   162,   163,   163,
     164,   165,   165,   165,   165,   166,   167,   167,   168,   169,
     169,   170,   170,   171,   171,   172,   173,   173,   174,   174,
     175,   176,   176,   176,   177,   177,   177,   177,   177,   178,
     178,   179,   180,   180,   181,   182,   182,   183,   183,   184,
     184,   184,   185,   186,   186,   186,   187,   187,   188,   188,
     188,   188,   188,   188,   189,   189,   190,   191,   191,   192,
     193,   193,   194,   195,   196,   197,   197,   198,   198,   199,
     199,   200,   201,   201,   202,   202,   203,   203,   204,   205,
     206,   207,   207,   207,   207,   208,   208,   209,   209,   210,
     211,   211,   212,   212,   212,   213,   213,   214,   215,   215,
     216,   216,   217,   217,   218,   218,   219,   220,   220,   221,
     221,   221,   222,   223,   223,   224,   224,   224,   225,   226,
     226,   227,   228,   229,   230,   230,   231,   231,   232,   233,
     233,   234,   234,   235,   235,   236,   236,   237,   237,   237,
     238,   238,   239,   239,   240,   241,   241,   242,   243,   243,
     244,   244,   245,   245,   245,   245,   246,   246,   246,   247,
     247,   248,   248,   248,   249,   249,   250,   251,   251,   252,
     252,   253,   253,   254,   254,   254,   254,   254,   254,   255,
     255,   256,   257,   258,   259,   260,   261,   262,   263,   263,
     264,   264,   265,   266,   267,   268,   269,   270,   271,   272,
     273,   274,   274,   275,   275,   275,   275,   275,   276,   277,
     277,   278,   279,   280,   280,   280,   280,   280,   281,   281,
     282,   282,   283,   284,   285,   286,   287,   287,   287,   288,
     289,   289,   290,   291,   292,   293,   294,   294,   295,   296,
     296,   297,   298,   299,   299,   300,   300,   301,   302,   303,
     303,   303,   304,   304,   305,   305,   306,   307,   307,   307,
     308,   308,   308,   308,   308,   308,   309,   310,   310,   310,
     310,   310,   311,   311,   312,   313,   313,   314,   315,   315,
     316,   316,   317,   318,   319,   319,   319,   320,   321,   322,
     323,   324,   325,   326,   327,   327,   327,   328
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     1,     1,     0,     2,     1,     1,     1,     1,
       1,     1,     1,     1,     8,     1,     8,     8,     8,     8,
       8,     3,     0,     1,     3,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     3,     1,     1,
       1,     3,     3,     3,     3,     3,     3,     1,     1,     1,
       1,     1,     1,     1,     1,     3,     2,     5,     1,     3,
       3,     1,     1,     2,     3,     1,     1,     1,     1,     1,
       1,     1,     1,     3,     1,     1,     1,     1,     3,     1,
       7,     1,     3,     1,     3,     1,     3,     3,     1,     3,
       1,     1,     3,     1,     1,     1,     1,     1,     1,     3,
       4,     4,     4,     1,     2,     0,     2,     2,     3,     3,
       1,     1,     1,     1,     1,     1,     1,     1,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     3,     1,
       1,     3,     3,     3,     3,     1,     1,     1,     1,     1,
       1,     1,     1,     3,     1,     6,     1,     3,     1,     1,
       3,     1,     1,     2,     3,     1,     1,     1,     1,     4,
       1,     1,     4,     1,     1,     3,     1,     4,     7,     1,
       3,     1,     3,     1,     3,     3,     1,     1,     1,     3,
       5,     1,     1,     1,     1,     1,     1,     1,     3,     1,
       3,     2,     0,     2,     2,     3,     3,     1,     1,     1,
       1,     3,     6,     1,     3,     1,     1,     3,     1,     1,
       1,     4,     3,     1,     1,     3,     3,     3,     3,     3,
       1,     3,     3,     3,     3,     3,     5,     1,     3,     1,
       1,     1,     3,     5,     1,     3,     1,     1,     1,     1,
       2,     1,     3,     1,     1,     1,     1,     1,     1,     6,
       1,     1,     1,     1,     1,     1,     1,     3,     1,     1,
       3,     3,     3,     3,     2,     1,     3,     1,     1,     1,
       1,     3,     6,     1,     3,     1,     1,     1,     1,     1,
       1,     1,     3,     1,     1,     4,     1,     1,     1,     1,
       4,     1,     4,     1,     3,     1,     1,     1,     1,     1,
       3,     3,     1,     3,     2,     0,     2,     2,     1,     3,
       1,     3,     1,     2,     4,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     2,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     3,     1,     3,
       1,     1,     7,     1,     7,     1,     1,     1,     1,     4,
       2,     0,     4,     1,     7,     1,     1,     3,     2,     0,
       2,     2,     2,     2,     0,     2,     0,     1,     4,     0,
       2,     4,     3,     1,     1,     3,     1,     1,     3,     1,
       1,     1,     1,     1,     1,     1,     4,     3,     3,     3,
       3,     3,     1,     3,     2,     0,     2,     2,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1
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
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2329 "parser.tab.c"
        break;

    case YYSYMBOL_BACK_QUOTED: /* BACK_QUOTED  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2335 "parser.tab.c"
        break;

    case YYSYMBOL_DISTINCT_OBJECT: /* DISTINCT_OBJECT  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2341 "parser.tab.c"
        break;

    case YYSYMBOL_DOLLAR_WORD: /* DOLLAR_WORD  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2347 "parser.tab.c"
        break;

    case YYSYMBOL_DOLLAR_DOLLAR_WORD: /* DOLLAR_DOLLAR_WORD  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2353 "parser.tab.c"
        break;

    case YYSYMBOL_UPPER_WORD: /* UPPER_WORD  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2359 "parser.tab.c"
        break;

    case YYSYMBOL_LOWER_WORD: /* LOWER_WORD  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2365 "parser.tab.c"
        break;

    case YYSYMBOL_REAL: /* REAL  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2371 "parser.tab.c"
        break;

    case YYSYMBOL_RATIONAL: /* RATIONAL  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2377 "parser.tab.c"
        break;

    case YYSYMBOL_INTEGER: /* INTEGER  */
#line 429 "parser.y"
            { free(((*yyvaluep).raw)); }
#line 2383 "parser.tab.c"
        break;

    case YYSYMBOL_tptp_file: /* tptp_file  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2389 "parser.tab.c"
        break;

    case YYSYMBOL_tptp_input_list: /* tptp_input_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2395 "parser.tab.c"
        break;

    case YYSYMBOL_tptp_input: /* tptp_input  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2401 "parser.tab.c"
        break;

    case YYSYMBOL_annotated_formula: /* annotated_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2407 "parser.tab.c"
        break;

    case YYSYMBOL_tpi_annotated: /* tpi_annotated  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2413 "parser.tab.c"
        break;

    case YYSYMBOL_tpi_formula: /* tpi_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2419 "parser.tab.c"
        break;

    case YYSYMBOL_thf_annotated: /* thf_annotated  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2425 "parser.tab.c"
        break;

    case YYSYMBOL_tff_annotated: /* tff_annotated  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2431 "parser.tab.c"
        break;

    case YYSYMBOL_tcf_annotated: /* tcf_annotated  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2437 "parser.tab.c"
        break;

    case YYSYMBOL_fof_annotated: /* fof_annotated  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2443 "parser.tab.c"
        break;

    case YYSYMBOL_cnf_annotated: /* cnf_annotated  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2449 "parser.tab.c"
        break;

    case YYSYMBOL_annotations: /* annotations  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2455 "parser.tab.c"
        break;

    case YYSYMBOL_formula_role: /* formula_role  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2461 "parser.tab.c"
        break;

    case YYSYMBOL_thf_formula: /* thf_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2467 "parser.tab.c"
        break;

    case YYSYMBOL_thf_logic_formula: /* thf_logic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2473 "parser.tab.c"
        break;

    case YYSYMBOL_thf_binary_formula: /* thf_binary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2479 "parser.tab.c"
        break;

    case YYSYMBOL_thf_binary_nonassoc: /* thf_binary_nonassoc  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2485 "parser.tab.c"
        break;

    case YYSYMBOL_thf_binary_assoc: /* thf_binary_assoc  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2491 "parser.tab.c"
        break;

    case YYSYMBOL_thf_or_formula: /* thf_or_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2497 "parser.tab.c"
        break;

    case YYSYMBOL_thf_and_formula: /* thf_and_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2503 "parser.tab.c"
        break;

    case YYSYMBOL_thf_apply_formula: /* thf_apply_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2509 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unit_formula: /* thf_unit_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2515 "parser.tab.c"
        break;

    case YYSYMBOL_thf_preunit_formula: /* thf_preunit_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2521 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unitary_formula: /* thf_unitary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2527 "parser.tab.c"
        break;

    case YYSYMBOL_thf_quantified_formula: /* thf_quantified_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2533 "parser.tab.c"
        break;

    case YYSYMBOL_thf_quantification: /* thf_quantification  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2539 "parser.tab.c"
        break;

    case YYSYMBOL_thf_variable_list: /* thf_variable_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2545 "parser.tab.c"
        break;

    case YYSYMBOL_thf_typed_variable: /* thf_typed_variable  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2551 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unary_formula: /* thf_unary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2557 "parser.tab.c"
        break;

    case YYSYMBOL_thf_prefix_unary: /* thf_prefix_unary  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2563 "parser.tab.c"
        break;

    case YYSYMBOL_thf_infix_unary: /* thf_infix_unary  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2569 "parser.tab.c"
        break;

    case YYSYMBOL_thf_atomic_formula: /* thf_atomic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2575 "parser.tab.c"
        break;

    case YYSYMBOL_thf_plain_atomic: /* thf_plain_atomic  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2581 "parser.tab.c"
        break;

    case YYSYMBOL_thf_defined_atomic: /* thf_defined_atomic  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2587 "parser.tab.c"
        break;

    case YYSYMBOL_thf_defined_term: /* thf_defined_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2593 "parser.tab.c"
        break;

    case YYSYMBOL_thf_defined_infix: /* thf_defined_infix  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2599 "parser.tab.c"
        break;

    case YYSYMBOL_thf_system_atomic: /* thf_system_atomic  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2605 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let: /* thf_let  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2611 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let_types: /* thf_let_types  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2617 "parser.tab.c"
        break;

    case YYSYMBOL_thf_atom_typing_list: /* thf_atom_typing_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2623 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let_defns: /* thf_let_defns  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2629 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let_defn: /* thf_let_defn  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2635 "parser.tab.c"
        break;

    case YYSYMBOL_thf_let_defn_list: /* thf_let_defn_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2641 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unitary_term: /* thf_unitary_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2647 "parser.tab.c"
        break;

    case YYSYMBOL_thf_conn_term: /* thf_conn_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2653 "parser.tab.c"
        break;

    case YYSYMBOL_thf_tuple: /* thf_tuple  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2659 "parser.tab.c"
        break;

    case YYSYMBOL_thf_fof_function: /* thf_fof_function  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2665 "parser.tab.c"
        break;

    case YYSYMBOL_thf_arguments: /* thf_arguments  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2671 "parser.tab.c"
        break;

    case YYSYMBOL_thf_formula_list: /* thf_formula_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2677 "parser.tab.c"
        break;

    case YYSYMBOL_comma_thf_logic_formula_list: /* comma_thf_logic_formula_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2683 "parser.tab.c"
        break;

    case YYSYMBOL_comma_thf_logic_formula: /* comma_thf_logic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2689 "parser.tab.c"
        break;

    case YYSYMBOL_thf_atom_typing: /* thf_atom_typing  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2695 "parser.tab.c"
        break;

    case YYSYMBOL_thf_top_level_type: /* thf_top_level_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2701 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unitary_type: /* thf_unitary_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2707 "parser.tab.c"
        break;

    case YYSYMBOL_thf_apply_type: /* thf_apply_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2713 "parser.tab.c"
        break;

    case YYSYMBOL_thf_binary_type: /* thf_binary_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2719 "parser.tab.c"
        break;

    case YYSYMBOL_thf_mapping_type: /* thf_mapping_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2725 "parser.tab.c"
        break;

    case YYSYMBOL_thf_xprod_type: /* thf_xprod_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2731 "parser.tab.c"
        break;

    case YYSYMBOL_thf_union_type: /* thf_union_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2737 "parser.tab.c"
        break;

    case YYSYMBOL_thf_subtype: /* thf_subtype  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2743 "parser.tab.c"
        break;

    case YYSYMBOL_thf_definition: /* thf_definition  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2749 "parser.tab.c"
        break;

    case YYSYMBOL_thf_sequent: /* thf_sequent  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2755 "parser.tab.c"
        break;

    case YYSYMBOL_tff_formula: /* tff_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2761 "parser.tab.c"
        break;

    case YYSYMBOL_tff_logic_formula: /* tff_logic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2767 "parser.tab.c"
        break;

    case YYSYMBOL_tff_binary_formula: /* tff_binary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2773 "parser.tab.c"
        break;

    case YYSYMBOL_tff_binary_nonassoc: /* tff_binary_nonassoc  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2779 "parser.tab.c"
        break;

    case YYSYMBOL_tff_binary_assoc: /* tff_binary_assoc  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2785 "parser.tab.c"
        break;

    case YYSYMBOL_tff_or_formula: /* tff_or_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2791 "parser.tab.c"
        break;

    case YYSYMBOL_tff_and_formula: /* tff_and_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2797 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unit_formula: /* tff_unit_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2803 "parser.tab.c"
        break;

    case YYSYMBOL_tff_preunit_formula: /* tff_preunit_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2809 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unitary_formula: /* tff_unitary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2815 "parser.tab.c"
        break;

    case YYSYMBOL_txf_unitary_formula: /* txf_unitary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2821 "parser.tab.c"
        break;

    case YYSYMBOL_tff_quantified_formula: /* tff_quantified_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2827 "parser.tab.c"
        break;

    case YYSYMBOL_tff_variable_list: /* tff_variable_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2833 "parser.tab.c"
        break;

    case YYSYMBOL_tff_variable: /* tff_variable  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2839 "parser.tab.c"
        break;

    case YYSYMBOL_tff_typed_variable: /* tff_typed_variable  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2845 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unary_formula: /* tff_unary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2851 "parser.tab.c"
        break;

    case YYSYMBOL_tff_prefix_unary: /* tff_prefix_unary  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2857 "parser.tab.c"
        break;

    case YYSYMBOL_tff_infix_unary: /* tff_infix_unary  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2863 "parser.tab.c"
        break;

    case YYSYMBOL_tff_atomic_formula: /* tff_atomic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2869 "parser.tab.c"
        break;

    case YYSYMBOL_tff_plain_atomic: /* tff_plain_atomic  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2875 "parser.tab.c"
        break;

    case YYSYMBOL_tff_defined_atomic: /* tff_defined_atomic  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2881 "parser.tab.c"
        break;

    case YYSYMBOL_tff_defined_plain: /* tff_defined_plain  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2887 "parser.tab.c"
        break;

    case YYSYMBOL_tff_defined_infix: /* tff_defined_infix  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2893 "parser.tab.c"
        break;

    case YYSYMBOL_tff_system_atomic: /* tff_system_atomic  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2899 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let: /* txf_let  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2905 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_types: /* txf_let_types  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2911 "parser.tab.c"
        break;

    case YYSYMBOL_tff_atom_typing_list: /* tff_atom_typing_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2917 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_defns: /* txf_let_defns  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2923 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_defn: /* txf_let_defn  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2929 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_LHS: /* txf_let_LHS  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2935 "parser.tab.c"
        break;

    case YYSYMBOL_txf_let_defn_list: /* txf_let_defn_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2941 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_atom: /* nxf_atom  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2947 "parser.tab.c"
        break;

    case YYSYMBOL_tff_term: /* tff_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2953 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unitary_term: /* tff_unitary_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2959 "parser.tab.c"
        break;

    case YYSYMBOL_txf_tuple: /* txf_tuple  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2965 "parser.tab.c"
        break;

    case YYSYMBOL_tff_arguments: /* tff_arguments  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2971 "parser.tab.c"
        break;

    case YYSYMBOL_comma_tff_term_list: /* comma_tff_term_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2977 "parser.tab.c"
        break;

    case YYSYMBOL_comma_tff_term: /* comma_tff_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2983 "parser.tab.c"
        break;

    case YYSYMBOL_tff_atom_typing: /* tff_atom_typing  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2989 "parser.tab.c"
        break;

    case YYSYMBOL_tff_top_level_type: /* tff_top_level_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 2995 "parser.tab.c"
        break;

    case YYSYMBOL_tff_non_atomic_type: /* tff_non_atomic_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3001 "parser.tab.c"
        break;

    case YYSYMBOL_tf1_quantified_type: /* tf1_quantified_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3007 "parser.tab.c"
        break;

    case YYSYMBOL_tff_monotype: /* tff_monotype  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3013 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unitary_type: /* tff_unitary_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3019 "parser.tab.c"
        break;

    case YYSYMBOL_tff_atomic_type: /* tff_atomic_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3025 "parser.tab.c"
        break;

    case YYSYMBOL_tff_type_arguments: /* tff_type_arguments  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3031 "parser.tab.c"
        break;

    case YYSYMBOL_tff_mapping_type: /* tff_mapping_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3037 "parser.tab.c"
        break;

    case YYSYMBOL_tff_xprod_type: /* tff_xprod_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3043 "parser.tab.c"
        break;

    case YYSYMBOL_txf_tuple_type: /* txf_tuple_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3049 "parser.tab.c"
        break;

    case YYSYMBOL_tff_type_list: /* tff_type_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3055 "parser.tab.c"
        break;

    case YYSYMBOL_tff_subtype: /* tff_subtype  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3061 "parser.tab.c"
        break;

    case YYSYMBOL_txf_definition: /* txf_definition  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3067 "parser.tab.c"
        break;

    case YYSYMBOL_txf_sequent: /* txf_sequent  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3073 "parser.tab.c"
        break;

    case YYSYMBOL_nhf_long_connective: /* nhf_long_connective  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3079 "parser.tab.c"
        break;

    case YYSYMBOL_nhf_parameter_list: /* nhf_parameter_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3085 "parser.tab.c"
        break;

    case YYSYMBOL_nhf_parameter: /* nhf_parameter  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3091 "parser.tab.c"
        break;

    case YYSYMBOL_nhf_key_pair: /* nhf_key_pair  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3097 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_long_connective: /* nxf_long_connective  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3103 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_parameter_list: /* nxf_parameter_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3109 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_parameter: /* nxf_parameter  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3115 "parser.tab.c"
        break;

    case YYSYMBOL_nxf_key_pair: /* nxf_key_pair  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3121 "parser.tab.c"
        break;

    case YYSYMBOL_ntf_connective_name: /* ntf_connective_name  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3127 "parser.tab.c"
        break;

    case YYSYMBOL_ntf_index: /* ntf_index  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3133 "parser.tab.c"
        break;

    case YYSYMBOL_ntf_short_connective: /* ntf_short_connective  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3139 "parser.tab.c"
        break;

    case YYSYMBOL_tcf_formula: /* tcf_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3145 "parser.tab.c"
        break;

    case YYSYMBOL_tcf_logic_formula: /* tcf_logic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3151 "parser.tab.c"
        break;

    case YYSYMBOL_tcf_quantified_formula: /* tcf_quantified_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3157 "parser.tab.c"
        break;

    case YYSYMBOL_fof_formula: /* fof_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3163 "parser.tab.c"
        break;

    case YYSYMBOL_fof_logic_formula: /* fof_logic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3169 "parser.tab.c"
        break;

    case YYSYMBOL_fof_binary_formula: /* fof_binary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3175 "parser.tab.c"
        break;

    case YYSYMBOL_fof_binary_nonassoc: /* fof_binary_nonassoc  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3181 "parser.tab.c"
        break;

    case YYSYMBOL_fof_binary_assoc: /* fof_binary_assoc  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3187 "parser.tab.c"
        break;

    case YYSYMBOL_fof_or_formula: /* fof_or_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3193 "parser.tab.c"
        break;

    case YYSYMBOL_fof_and_formula: /* fof_and_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3199 "parser.tab.c"
        break;

    case YYSYMBOL_fof_unary_formula: /* fof_unary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3205 "parser.tab.c"
        break;

    case YYSYMBOL_fof_infix_unary: /* fof_infix_unary  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3211 "parser.tab.c"
        break;

    case YYSYMBOL_fof_unit_formula: /* fof_unit_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3217 "parser.tab.c"
        break;

    case YYSYMBOL_fof_unitary_formula: /* fof_unitary_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3223 "parser.tab.c"
        break;

    case YYSYMBOL_fof_quantified_formula: /* fof_quantified_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3229 "parser.tab.c"
        break;

    case YYSYMBOL_fof_variable_list: /* fof_variable_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3235 "parser.tab.c"
        break;

    case YYSYMBOL_fof_atomic_formula: /* fof_atomic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3241 "parser.tab.c"
        break;

    case YYSYMBOL_fof_plain_atomic_formula: /* fof_plain_atomic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3247 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_atomic_formula: /* fof_defined_atomic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3253 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_plain_formula: /* fof_defined_plain_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3259 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_infix_formula: /* fof_defined_infix_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3265 "parser.tab.c"
        break;

    case YYSYMBOL_fof_system_atomic_formula: /* fof_system_atomic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3271 "parser.tab.c"
        break;

    case YYSYMBOL_fof_plain_term: /* fof_plain_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3277 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_term: /* fof_defined_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3283 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_atomic_term: /* fof_defined_atomic_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3289 "parser.tab.c"
        break;

    case YYSYMBOL_fof_defined_plain_term: /* fof_defined_plain_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3295 "parser.tab.c"
        break;

    case YYSYMBOL_fof_system_term: /* fof_system_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3301 "parser.tab.c"
        break;

    case YYSYMBOL_fof_arguments: /* fof_arguments  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3307 "parser.tab.c"
        break;

    case YYSYMBOL_fof_term: /* fof_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3313 "parser.tab.c"
        break;

    case YYSYMBOL_fof_function_term: /* fof_function_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3319 "parser.tab.c"
        break;

    case YYSYMBOL_fof_sequent: /* fof_sequent  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3325 "parser.tab.c"
        break;

    case YYSYMBOL_fof_formula_tuple: /* fof_formula_tuple  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3331 "parser.tab.c"
        break;

    case YYSYMBOL_fof_formula_tuple_list: /* fof_formula_tuple_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3337 "parser.tab.c"
        break;

    case YYSYMBOL_comma_fof_logic_formula_list: /* comma_fof_logic_formula_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3343 "parser.tab.c"
        break;

    case YYSYMBOL_comma_fof_logic_formula: /* comma_fof_logic_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3349 "parser.tab.c"
        break;

    case YYSYMBOL_cnf_formula: /* cnf_formula  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3355 "parser.tab.c"
        break;

    case YYSYMBOL_cnf_disjunction: /* cnf_disjunction  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3361 "parser.tab.c"
        break;

    case YYSYMBOL_cnf_literal: /* cnf_literal  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3367 "parser.tab.c"
        break;

    case YYSYMBOL_thf_quantifier: /* thf_quantifier  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3373 "parser.tab.c"
        break;

    case YYSYMBOL_thf_unary_connective: /* thf_unary_connective  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3379 "parser.tab.c"
        break;

    case YYSYMBOL_th0_quantifier: /* th0_quantifier  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3385 "parser.tab.c"
        break;

    case YYSYMBOL_type_quantifier: /* type_quantifier  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3391 "parser.tab.c"
        break;

    case YYSYMBOL_subtype_sign: /* subtype_sign  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3397 "parser.tab.c"
        break;

    case YYSYMBOL_tff_unary_connective: /* tff_unary_connective  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3403 "parser.tab.c"
        break;

    case YYSYMBOL_tff_quantifier: /* tff_quantifier  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3409 "parser.tab.c"
        break;

    case YYSYMBOL_fof_quantifier: /* fof_quantifier  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3415 "parser.tab.c"
        break;

    case YYSYMBOL_nonassoc_connective: /* nonassoc_connective  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3421 "parser.tab.c"
        break;

    case YYSYMBOL_assoc_connective: /* assoc_connective  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3427 "parser.tab.c"
        break;

    case YYSYMBOL_unary_connective: /* unary_connective  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3433 "parser.tab.c"
        break;

    case YYSYMBOL_gentzen_arrow: /* gentzen_arrow  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3439 "parser.tab.c"
        break;

    case YYSYMBOL_assignment: /* assignment  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3445 "parser.tab.c"
        break;

    case YYSYMBOL_identical: /* identical  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3451 "parser.tab.c"
        break;

    case YYSYMBOL_type_constant: /* type_constant  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3457 "parser.tab.c"
        break;

    case YYSYMBOL_type_functor: /* type_functor  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3463 "parser.tab.c"
        break;

    case YYSYMBOL_defined_type: /* defined_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3469 "parser.tab.c"
        break;

    case YYSYMBOL_atom: /* atom  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3475 "parser.tab.c"
        break;

    case YYSYMBOL_untyped_atom: /* untyped_atom  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3481 "parser.tab.c"
        break;

    case YYSYMBOL_defined_infix_pred: /* defined_infix_pred  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3487 "parser.tab.c"
        break;

    case YYSYMBOL_infix_equality: /* infix_equality  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3493 "parser.tab.c"
        break;

    case YYSYMBOL_infix_inequality: /* infix_inequality  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3499 "parser.tab.c"
        break;

    case YYSYMBOL_constant: /* constant  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3505 "parser.tab.c"
        break;

    case YYSYMBOL_functor: /* functor  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3511 "parser.tab.c"
        break;

    case YYSYMBOL_defined_constant: /* defined_constant  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3517 "parser.tab.c"
        break;

    case YYSYMBOL_defined_functor: /* defined_functor  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3523 "parser.tab.c"
        break;

    case YYSYMBOL_system_constant: /* system_constant  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3529 "parser.tab.c"
        break;

    case YYSYMBOL_system_functor: /* system_functor  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3535 "parser.tab.c"
        break;

    case YYSYMBOL_def_or_sys_constant: /* def_or_sys_constant  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3541 "parser.tab.c"
        break;

    case YYSYMBOL_th1_defined_term: /* th1_defined_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3547 "parser.tab.c"
        break;

    case YYSYMBOL_distinct_object: /* distinct_object  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3553 "parser.tab.c"
        break;

    case YYSYMBOL_defined_term: /* defined_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3559 "parser.tab.c"
        break;

    case YYSYMBOL_upper_word: /* upper_word  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3565 "parser.tab.c"
        break;

    case YYSYMBOL_variable: /* variable  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3571 "parser.tab.c"
        break;

    case YYSYMBOL_source: /* source  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3577 "parser.tab.c"
        break;

    case YYSYMBOL_sources: /* sources  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3583 "parser.tab.c"
        break;

    case YYSYMBOL_dag_source: /* dag_source  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3589 "parser.tab.c"
        break;

    case YYSYMBOL_inference_record: /* inference_record  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3595 "parser.tab.c"
        break;

    case YYSYMBOL_inference_rule: /* inference_rule  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3601 "parser.tab.c"
        break;

    case YYSYMBOL_internal_source: /* internal_source  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3607 "parser.tab.c"
        break;

    case YYSYMBOL_intro_type: /* intro_type  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3613 "parser.tab.c"
        break;

    case YYSYMBOL_external_source: /* external_source  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3619 "parser.tab.c"
        break;

    case YYSYMBOL_file_source: /* file_source  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3625 "parser.tab.c"
        break;

    case YYSYMBOL_file_info: /* file_info  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3631 "parser.tab.c"
        break;

    case YYSYMBOL_theory: /* theory  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3637 "parser.tab.c"
        break;

    case YYSYMBOL_theory_name: /* theory_name  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3643 "parser.tab.c"
        break;

    case YYSYMBOL_creator_source: /* creator_source  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3649 "parser.tab.c"
        break;

    case YYSYMBOL_creator_name: /* creator_name  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3655 "parser.tab.c"
        break;

    case YYSYMBOL_parents: /* parents  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3661 "parser.tab.c"
        break;

    case YYSYMBOL_parent_list: /* parent_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3667 "parser.tab.c"
        break;

    case YYSYMBOL_comma_parent_info_list: /* comma_parent_info_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3673 "parser.tab.c"
        break;

    case YYSYMBOL_comma_parent_info: /* comma_parent_info  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3679 "parser.tab.c"
        break;

    case YYSYMBOL_parent_info: /* parent_info  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3685 "parser.tab.c"
        break;

    case YYSYMBOL_parent_details: /* parent_details  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3691 "parser.tab.c"
        break;

    case YYSYMBOL_optional_info: /* optional_info  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3697 "parser.tab.c"
        break;

    case YYSYMBOL_useful_info: /* useful_info  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3703 "parser.tab.c"
        break;

    case YYSYMBOL_include: /* include  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3709 "parser.tab.c"
        break;

    case YYSYMBOL_include_optionals: /* include_optionals  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3715 "parser.tab.c"
        break;

    case YYSYMBOL_formula_selection: /* formula_selection  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3721 "parser.tab.c"
        break;

    case YYSYMBOL_name_list: /* name_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3727 "parser.tab.c"
        break;

    case YYSYMBOL_space_name: /* space_name  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3733 "parser.tab.c"
        break;

    case YYSYMBOL_general_term: /* general_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3739 "parser.tab.c"
        break;

    case YYSYMBOL_general_data: /* general_data  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3745 "parser.tab.c"
        break;

    case YYSYMBOL_general_function: /* general_function  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3751 "parser.tab.c"
        break;

    case YYSYMBOL_formula_data: /* formula_data  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3757 "parser.tab.c"
        break;

    case YYSYMBOL_general_list: /* general_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3763 "parser.tab.c"
        break;

    case YYSYMBOL_general_terms: /* general_terms  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3769 "parser.tab.c"
        break;

    case YYSYMBOL_comma_general_term_list: /* comma_general_term_list  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3775 "parser.tab.c"
        break;

    case YYSYMBOL_comma_general_term: /* comma_general_term  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3781 "parser.tab.c"
        break;

    case YYSYMBOL_name: /* name  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3787 "parser.tab.c"
        break;

    case YYSYMBOL_lower_word: /* lower_word  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3793 "parser.tab.c"
        break;

    case YYSYMBOL_single_quoted: /* single_quoted  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3799 "parser.tab.c"
        break;

    case YYSYMBOL_back_quoted: /* back_quoted  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3805 "parser.tab.c"
        break;

    case YYSYMBOL_atomic_word: /* atomic_word  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3811 "parser.tab.c"
        break;

    case YYSYMBOL_dollar_word: /* dollar_word  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3817 "parser.tab.c"
        break;

    case YYSYMBOL_dollar_dollar_word: /* dollar_dollar_word  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3823 "parser.tab.c"
        break;

    case YYSYMBOL_atomic_defined_word: /* atomic_defined_word  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3829 "parser.tab.c"
        break;

    case YYSYMBOL_atomic_system_word: /* atomic_system_word  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3835 "parser.tab.c"
        break;

    case YYSYMBOL_integer: /* integer  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3841 "parser.tab.c"
        break;

    case YYSYMBOL_rational: /* rational  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3847 "parser.tab.c"
        break;

    case YYSYMBOL_real: /* real  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3853 "parser.tab.c"
        break;

    case YYSYMBOL_number: /* number  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3859 "parser.tab.c"
        break;

    case YYSYMBOL_file_name: /* file_name  */
#line 430 "parser.y"
            { lean_dec(((*yyvaluep).data)); }
#line 3865 "parser.tab.c"
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
#line 437 "parser.y"
            { context->result = (yyvsp[0].data); }
#line 4141 "parser.tab.c"
    break;

  case 3: /* tptp_file: tptp_input_list  */
#line 441 "parser.y"
                  { (yyval.data) = Tptp_mk_TptpFile_mk(lean_array_to_list((yyvsp[0].data))); }
#line 4147 "parser.tab.c"
    break;

  case 4: /* tptp_input_list: %empty  */
#line 445 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 4153 "parser.tab.c"
    break;

  case 5: /* tptp_input_list: tptp_input_list tptp_input  */
#line 446 "parser.y"
                               { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4159 "parser.tab.c"
    break;

  case 6: /* tptp_input: annotated_formula  */
#line 450 "parser.y"
                    { (yyval.data) = Tptp_mk_TptpInput_annotatedFormula((yyvsp[0].data)); }
#line 4165 "parser.tab.c"
    break;

  case 7: /* tptp_input: include  */
#line 451 "parser.y"
            { (yyval.data) = Tptp_mk_TptpInput_include((yyvsp[0].data)); }
#line 4171 "parser.tab.c"
    break;

  case 8: /* annotated_formula: thf_annotated  */
#line 455 "parser.y"
                { (yyval.data) = Tptp_mk_AnnotatedFormula_thfAnnotated((yyvsp[0].data)); }
#line 4177 "parser.tab.c"
    break;

  case 9: /* annotated_formula: tff_annotated  */
#line 456 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_tffAnnotated((yyvsp[0].data)); }
#line 4183 "parser.tab.c"
    break;

  case 10: /* annotated_formula: tcf_annotated  */
#line 457 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_tcfAnnotated((yyvsp[0].data)); }
#line 4189 "parser.tab.c"
    break;

  case 11: /* annotated_formula: fof_annotated  */
#line 458 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_fofAnnotated((yyvsp[0].data)); }
#line 4195 "parser.tab.c"
    break;

  case 12: /* annotated_formula: cnf_annotated  */
#line 459 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_cnfAnnotated((yyvsp[0].data)); }
#line 4201 "parser.tab.c"
    break;

  case 13: /* annotated_formula: tpi_annotated  */
#line 460 "parser.y"
                  { (yyval.data) = Tptp_mk_AnnotatedFormula_tpiAnnotated((yyvsp[0].data)); }
#line 4207 "parser.tab.c"
    break;

  case 14: /* tpi_annotated: "tpi(" name "," formula_role "," tpi_formula annotations ")."  */
#line 464 "parser.y"
                                                                { (yyval.data) = Tptp_mk_TpiAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4213 "parser.tab.c"
    break;

  case 15: /* tpi_formula: fof_formula  */
#line 468 "parser.y"
              { (yyval.data) = Tptp_mk_TpiFormula_mk((yyvsp[0].data)); }
#line 4219 "parser.tab.c"
    break;

  case 16: /* thf_annotated: "thf(" name "," formula_role "," thf_formula annotations ")."  */
#line 472 "parser.y"
                                                                { (yyval.data) = Tptp_mk_ThfAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4225 "parser.tab.c"
    break;

  case 17: /* tff_annotated: "tff(" name "," formula_role "," tff_formula annotations ")."  */
#line 476 "parser.y"
                                                                { (yyval.data) = Tptp_mk_TffAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4231 "parser.tab.c"
    break;

  case 18: /* tcf_annotated: "tcf(" name "," formula_role "," tcf_formula annotations ")."  */
#line 480 "parser.y"
                                                                { (yyval.data) = Tptp_mk_TcfAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4237 "parser.tab.c"
    break;

  case 19: /* fof_annotated: "fof(" name "," formula_role "," fof_formula annotations ")."  */
#line 484 "parser.y"
                                                                { (yyval.data) = Tptp_mk_FofAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4243 "parser.tab.c"
    break;

  case 20: /* cnf_annotated: "cnf(" name "," formula_role "," cnf_formula annotations ")."  */
#line 488 "parser.y"
                                                                { (yyval.data) = Tptp_mk_CnfAnnotated_mk((yyvsp[-6].data), (yyvsp[-4].data), (yyvsp[-2].data), (yyvsp[-1].data)); }
#line 4249 "parser.tab.c"
    break;

  case 21: /* annotations: "," source optional_info  */
#line 492 "parser.y"
                           { (yyval.data) = Tptp_mk_Annotations_sourceOptionalInfo((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4255 "parser.tab.c"
    break;

  case 22: /* annotations: %empty  */
#line 493 "parser.y"
           { (yyval.data) = Tptp_mk_Annotations_nothing; }
#line 4261 "parser.tab.c"
    break;

  case 23: /* formula_role: lower_word  */
#line 497 "parser.y"
             { (yyval.data) = Tptp_mk_FormulaRole_lowerWord((yyvsp[0].data)); }
#line 4267 "parser.tab.c"
    break;

  case 24: /* formula_role: lower_word "-" general_term  */
#line 498 "parser.y"
                                { (yyval.data) = Tptp_mk_FormulaRole_lowerWordGeneralTerm((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4273 "parser.tab.c"
    break;

  case 25: /* thf_formula: thf_logic_formula  */
#line 502 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfFormula_thfLogicFormula((yyvsp[0].data)); }
#line 4279 "parser.tab.c"
    break;

  case 26: /* thf_formula: thf_atom_typing  */
#line 503 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfFormula_thfAtomTyping((yyvsp[0].data)); }
#line 4285 "parser.tab.c"
    break;

  case 27: /* thf_formula: thf_subtype  */
#line 504 "parser.y"
                { (yyval.data) = Tptp_mk_ThfFormula_thfSubtype((yyvsp[0].data)); }
#line 4291 "parser.tab.c"
    break;

  case 28: /* thf_logic_formula: thf_unitary_formula  */
#line 508 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfLogicFormula_thfUnitaryFormula((yyvsp[0].data)); }
#line 4297 "parser.tab.c"
    break;

  case 29: /* thf_logic_formula: thf_unary_formula  */
#line 509 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfLogicFormula_thfUnaryFormula((yyvsp[0].data)); }
#line 4303 "parser.tab.c"
    break;

  case 30: /* thf_logic_formula: thf_binary_formula  */
#line 510 "parser.y"
                       { (yyval.data) = Tptp_mk_ThfLogicFormula_thfBinaryFormula((yyvsp[0].data)); }
#line 4309 "parser.tab.c"
    break;

  case 31: /* thf_logic_formula: thf_defined_infix  */
#line 511 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfLogicFormula_thfDefinedInfix((yyvsp[0].data)); }
#line 4315 "parser.tab.c"
    break;

  case 32: /* thf_logic_formula: thf_definition  */
#line 512 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfLogicFormula_thfDefinition((yyvsp[0].data)); }
#line 4321 "parser.tab.c"
    break;

  case 33: /* thf_logic_formula: thf_sequent  */
#line 513 "parser.y"
                { (yyval.data) = Tptp_mk_ThfLogicFormula_thfSequent((yyvsp[0].data)); }
#line 4327 "parser.tab.c"
    break;

  case 34: /* thf_binary_formula: thf_binary_nonassoc  */
#line 517 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfBinaryFormula_thfBinaryNonassoc((yyvsp[0].data)); }
#line 4333 "parser.tab.c"
    break;

  case 35: /* thf_binary_formula: thf_binary_assoc  */
#line 518 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfBinaryFormula_thfBinaryAssoc((yyvsp[0].data)); }
#line 4339 "parser.tab.c"
    break;

  case 36: /* thf_binary_formula: thf_binary_type  */
#line 519 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfBinaryFormula_thfBinaryType((yyvsp[0].data)); }
#line 4345 "parser.tab.c"
    break;

  case 37: /* thf_binary_nonassoc: thf_unit_formula nonassoc_connective thf_unit_formula  */
#line 523 "parser.y"
                                                        { (yyval.data) = Tptp_mk_ThfBinaryNonassoc_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4351 "parser.tab.c"
    break;

  case 38: /* thf_binary_assoc: thf_or_formula  */
#line 527 "parser.y"
                 { (yyval.data) = Tptp_mk_ThfBinaryAssoc_thfOrFormula((yyvsp[0].data)); }
#line 4357 "parser.tab.c"
    break;

  case 39: /* thf_binary_assoc: thf_and_formula  */
#line 528 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfBinaryAssoc_thfAndFormula((yyvsp[0].data)); }
#line 4363 "parser.tab.c"
    break;

  case 40: /* thf_binary_assoc: thf_apply_formula  */
#line 529 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfBinaryAssoc_thfApplyFormula((yyvsp[0].data)); }
#line 4369 "parser.tab.c"
    break;

  case 41: /* thf_or_formula: thf_unit_formula "|" thf_unit_formula  */
#line 533 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfOrFormula_thfUnitFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4375 "parser.tab.c"
    break;

  case 42: /* thf_or_formula: thf_or_formula "|" thf_unit_formula  */
#line 534 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfOrFormula_thfOrFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4381 "parser.tab.c"
    break;

  case 43: /* thf_and_formula: thf_unit_formula "&" thf_unit_formula  */
#line 538 "parser.y"
                                        { (yyval.data) = Tptp_mk_ThfAndFormula_thfUnitFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4387 "parser.tab.c"
    break;

  case 44: /* thf_and_formula: thf_and_formula "&" thf_unit_formula  */
#line 539 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfAndFormula_thfAndFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4393 "parser.tab.c"
    break;

  case 45: /* thf_apply_formula: thf_unit_formula "@" thf_unit_formula  */
#line 543 "parser.y"
                                        { (yyval.data) = Tptp_mk_ThfApplyFormula_thfUnitFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4399 "parser.tab.c"
    break;

  case 46: /* thf_apply_formula: thf_apply_formula "@" thf_unit_formula  */
#line 544 "parser.y"
                                           { (yyval.data) = Tptp_mk_ThfApplyFormula_thfApplyFormulaThfUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4405 "parser.tab.c"
    break;

  case 47: /* thf_unit_formula: thf_unitary_formula  */
#line 548 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfUnitFormula_thfUnitaryFormula((yyvsp[0].data)); }
#line 4411 "parser.tab.c"
    break;

  case 48: /* thf_unit_formula: thf_unary_formula  */
#line 549 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfUnitFormula_thfUnaryFormula((yyvsp[0].data)); }
#line 4417 "parser.tab.c"
    break;

  case 49: /* thf_unit_formula: thf_defined_infix  */
#line 550 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfUnitFormula_thfDefinedInfix((yyvsp[0].data)); }
#line 4423 "parser.tab.c"
    break;

  case 50: /* thf_preunit_formula: thf_unitary_formula  */
#line 554 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfPreunitFormula_thfUnitaryFormula((yyvsp[0].data)); }
#line 4429 "parser.tab.c"
    break;

  case 51: /* thf_preunit_formula: thf_prefix_unary  */
#line 555 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfPreunitFormula_thfPrefixUnary((yyvsp[0].data)); }
#line 4435 "parser.tab.c"
    break;

  case 52: /* thf_unitary_formula: thf_quantified_formula  */
#line 559 "parser.y"
                         { (yyval.data) = Tptp_mk_ThfUnitaryFormula_thfQuantifiedFormula((yyvsp[0].data)); }
#line 4441 "parser.tab.c"
    break;

  case 53: /* thf_unitary_formula: thf_atomic_formula  */
#line 560 "parser.y"
                       { (yyval.data) = Tptp_mk_ThfUnitaryFormula_thfAtomicFormula((yyvsp[0].data)); }
#line 4447 "parser.tab.c"
    break;

  case 54: /* thf_unitary_formula: variable  */
#line 561 "parser.y"
             { (yyval.data) = Tptp_mk_ThfUnitaryFormula_variable((yyvsp[0].data)); }
#line 4453 "parser.tab.c"
    break;

  case 55: /* thf_unitary_formula: "(" thf_logic_formula ")"  */
#line 562 "parser.y"
                              { (yyval.data) = Tptp_mk_ThfUnitaryFormula_thfLogicFormula((yyvsp[-1].data)); }
#line 4459 "parser.tab.c"
    break;

  case 56: /* thf_quantified_formula: thf_quantification thf_unit_formula  */
#line 566 "parser.y"
                                      { (yyval.data) = Tptp_mk_ThfQuantifiedFormula_mk((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4465 "parser.tab.c"
    break;

  case 57: /* thf_quantification: thf_quantifier "[" thf_variable_list "]" ":"  */
#line 570 "parser.y"
                                               { (yyval.data) = Tptp_mk_ThfQuantification_mk((yyvsp[-4].data), (yyvsp[-2].data)); }
#line 4471 "parser.tab.c"
    break;

  case 58: /* thf_variable_list: thf_typed_variable  */
#line 574 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfVariableList_thfTypedVariable((yyvsp[0].data)); }
#line 4477 "parser.tab.c"
    break;

  case 59: /* thf_variable_list: thf_typed_variable "," thf_variable_list  */
#line 575 "parser.y"
                                             { (yyval.data) = Tptp_mk_ThfVariableList_thfTypedVariableThfVariableList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4483 "parser.tab.c"
    break;

  case 60: /* thf_typed_variable: variable ":" thf_top_level_type  */
#line 579 "parser.y"
                                  { (yyval.data) = Tptp_mk_ThfTypedVariable_mk((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4489 "parser.tab.c"
    break;

  case 61: /* thf_unary_formula: thf_prefix_unary  */
#line 583 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfUnaryFormula_thfPrefixUnary((yyvsp[0].data)); }
#line 4495 "parser.tab.c"
    break;

  case 62: /* thf_unary_formula: thf_infix_unary  */
#line 584 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfUnaryFormula_thfInfixUnary((yyvsp[0].data)); }
#line 4501 "parser.tab.c"
    break;

  case 63: /* thf_prefix_unary: thf_unary_connective thf_preunit_formula  */
#line 588 "parser.y"
                                           { (yyval.data) = Tptp_mk_ThfPrefixUnary_mk((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4507 "parser.tab.c"
    break;

  case 64: /* thf_infix_unary: thf_unitary_term infix_inequality thf_unitary_term  */
#line 592 "parser.y"
                                                     { (yyval.data) = Tptp_mk_ThfInfixUnary_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4513 "parser.tab.c"
    break;

  case 65: /* thf_atomic_formula: thf_plain_atomic  */
#line 596 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfAtomicFormula_thfPlainAtomic((yyvsp[0].data)); }
#line 4519 "parser.tab.c"
    break;

  case 66: /* thf_atomic_formula: thf_defined_atomic  */
#line 597 "parser.y"
                       { (yyval.data) = Tptp_mk_ThfAtomicFormula_thfDefinedAtomic((yyvsp[0].data)); }
#line 4525 "parser.tab.c"
    break;

  case 67: /* thf_atomic_formula: thf_system_atomic  */
#line 598 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfAtomicFormula_thfSystemAtomic((yyvsp[0].data)); }
#line 4531 "parser.tab.c"
    break;

  case 68: /* thf_atomic_formula: thf_fof_function  */
#line 599 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfAtomicFormula_thfFofFunction((yyvsp[0].data)); }
#line 4537 "parser.tab.c"
    break;

  case 69: /* thf_plain_atomic: constant  */
#line 603 "parser.y"
           { (yyval.data) = Tptp_mk_ThfPlainAtomic_constant((yyvsp[0].data)); }
#line 4543 "parser.tab.c"
    break;

  case 70: /* thf_plain_atomic: thf_tuple  */
#line 604 "parser.y"
              { (yyval.data) = Tptp_mk_ThfPlainAtomic_thfTuple((yyvsp[0].data)); }
#line 4549 "parser.tab.c"
    break;

  case 71: /* thf_defined_atomic: defined_constant  */
#line 608 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfDefinedAtomic_definedConstant((yyvsp[0].data)); }
#line 4555 "parser.tab.c"
    break;

  case 72: /* thf_defined_atomic: thf_defined_term  */
#line 609 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfDefinedAtomic_thfDefinedTerm((yyvsp[0].data)); }
#line 4561 "parser.tab.c"
    break;

  case 73: /* thf_defined_atomic: "(" thf_conn_term ")"  */
#line 610 "parser.y"
                          { (yyval.data) = Tptp_mk_ThfDefinedAtomic_thfConnTerm((yyvsp[-1].data)); }
#line 4567 "parser.tab.c"
    break;

  case 74: /* thf_defined_atomic: nhf_long_connective  */
#line 611 "parser.y"
                        { (yyval.data) = Tptp_mk_ThfDefinedAtomic_nhfLongConnective((yyvsp[0].data)); }
#line 4573 "parser.tab.c"
    break;

  case 75: /* thf_defined_atomic: thf_let  */
#line 612 "parser.y"
            { (yyval.data) = Tptp_mk_ThfDefinedAtomic_thfLet((yyvsp[0].data)); }
#line 4579 "parser.tab.c"
    break;

  case 76: /* thf_defined_term: defined_term  */
#line 616 "parser.y"
               { (yyval.data) = Tptp_mk_ThfDefinedTerm_definedTerm((yyvsp[0].data)); }
#line 4585 "parser.tab.c"
    break;

  case 77: /* thf_defined_term: th1_defined_term  */
#line 617 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfDefinedTerm_th1DefinedTerm((yyvsp[0].data)); }
#line 4591 "parser.tab.c"
    break;

  case 78: /* thf_defined_infix: thf_unitary_term defined_infix_pred thf_unitary_term  */
#line 621 "parser.y"
                                                       { (yyval.data) = Tptp_mk_ThfDefinedInfix_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4597 "parser.tab.c"
    break;

  case 79: /* thf_system_atomic: system_constant  */
#line 625 "parser.y"
                  { (yyval.data) = Tptp_mk_ThfSystemAtomic_mk((yyvsp[0].data)); }
#line 4603 "parser.tab.c"
    break;

  case 80: /* thf_let: "$let(" thf_let_types "," thf_let_defns "," thf_logic_formula ")"  */
#line 629 "parser.y"
                                                                    { (yyval.data) = Tptp_mk_ThfLet_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 4609 "parser.tab.c"
    break;

  case 81: /* thf_let_types: thf_atom_typing  */
#line 633 "parser.y"
                  { (yyval.data) = Tptp_mk_ThfLetTypes_thfAtomTyping((yyvsp[0].data)); }
#line 4615 "parser.tab.c"
    break;

  case 82: /* thf_let_types: "[" thf_atom_typing_list "]"  */
#line 634 "parser.y"
                                 { (yyval.data) = Tptp_mk_ThfLetTypes_thfAtomTypingList((yyvsp[-1].data)); }
#line 4621 "parser.tab.c"
    break;

  case 83: /* thf_atom_typing_list: thf_atom_typing  */
#line 638 "parser.y"
                  { (yyval.data) = Tptp_mk_ThfAtomTypingList_thfAtomTyping((yyvsp[0].data)); }
#line 4627 "parser.tab.c"
    break;

  case 84: /* thf_atom_typing_list: thf_atom_typing "," thf_atom_typing_list  */
#line 639 "parser.y"
                                             { (yyval.data) = Tptp_mk_ThfAtomTypingList_thfAtomTypingThfAtomTypingList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4633 "parser.tab.c"
    break;

  case 85: /* thf_let_defns: thf_let_defn  */
#line 643 "parser.y"
               { (yyval.data) = Tptp_mk_ThfLetDefns_thfLetDefn((yyvsp[0].data)); }
#line 4639 "parser.tab.c"
    break;

  case 86: /* thf_let_defns: "[" thf_let_defn_list "]"  */
#line 644 "parser.y"
                              { (yyval.data) = Tptp_mk_ThfLetDefns_thfLetDefnList((yyvsp[-1].data)); }
#line 4645 "parser.tab.c"
    break;

  case 87: /* thf_let_defn: thf_logic_formula assignment thf_logic_formula  */
#line 648 "parser.y"
                                                 { (yyval.data) = Tptp_mk_ThfLetDefn_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4651 "parser.tab.c"
    break;

  case 88: /* thf_let_defn_list: thf_let_defn  */
#line 652 "parser.y"
               { (yyval.data) = Tptp_mk_ThfLetDefnList_thfLetDefn((yyvsp[0].data)); }
#line 4657 "parser.tab.c"
    break;

  case 89: /* thf_let_defn_list: thf_let_defn "," thf_let_defn_list  */
#line 653 "parser.y"
                                       { (yyval.data) = Tptp_mk_ThfLetDefnList_thfLetDefnThfLetDefnList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4663 "parser.tab.c"
    break;

  case 90: /* thf_unitary_term: thf_atomic_formula  */
#line 657 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfUnitaryTerm_thfAtomicFormula((yyvsp[0].data)); }
#line 4669 "parser.tab.c"
    break;

  case 91: /* thf_unitary_term: variable  */
#line 658 "parser.y"
             { (yyval.data) = Tptp_mk_ThfUnitaryTerm_variable((yyvsp[0].data)); }
#line 4675 "parser.tab.c"
    break;

  case 92: /* thf_unitary_term: "(" thf_logic_formula ")"  */
#line 659 "parser.y"
                              { (yyval.data) = Tptp_mk_ThfUnitaryTerm_thfLogicFormula((yyvsp[-1].data)); }
#line 4681 "parser.tab.c"
    break;

  case 93: /* thf_conn_term: nonassoc_connective  */
#line 663 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfConnTerm_nonassocConnective((yyvsp[0].data)); }
#line 4687 "parser.tab.c"
    break;

  case 94: /* thf_conn_term: assoc_connective  */
#line 664 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfConnTerm_assocConnective((yyvsp[0].data)); }
#line 4693 "parser.tab.c"
    break;

  case 95: /* thf_conn_term: infix_equality  */
#line 665 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfConnTerm_infixEquality((yyvsp[0].data)); }
#line 4699 "parser.tab.c"
    break;

  case 96: /* thf_conn_term: infix_inequality  */
#line 666 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfConnTerm_infixInequality((yyvsp[0].data)); }
#line 4705 "parser.tab.c"
    break;

  case 97: /* thf_conn_term: thf_unary_connective  */
#line 667 "parser.y"
                         { (yyval.data) = Tptp_mk_ThfConnTerm_thfUnaryConnective((yyvsp[0].data)); }
#line 4711 "parser.tab.c"
    break;

  case 98: /* thf_tuple: "[]"  */
#line 671 "parser.y"
       { (yyval.data) = Tptp_mk_ThfTuple_empty; }
#line 4717 "parser.tab.c"
    break;

  case 99: /* thf_tuple: "[" thf_formula_list "]"  */
#line 672 "parser.y"
                             { (yyval.data) = Tptp_mk_ThfTuple_thfFormulaList((yyvsp[-1].data)); }
#line 4723 "parser.tab.c"
    break;

  case 100: /* thf_fof_function: functor "(" thf_arguments ")"  */
#line 676 "parser.y"
                                { (yyval.data) = Tptp_mk_ThfFofFunction_functorThfArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 4729 "parser.tab.c"
    break;

  case 101: /* thf_fof_function: defined_functor "(" thf_arguments ")"  */
#line 677 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfFofFunction_definedFunctorThfArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 4735 "parser.tab.c"
    break;

  case 102: /* thf_fof_function: system_functor "(" thf_arguments ")"  */
#line 678 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfFofFunction_systemFunctorThfArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 4741 "parser.tab.c"
    break;

  case 103: /* thf_arguments: thf_formula_list  */
#line 682 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfArguments_mk((yyvsp[0].data)); }
#line 4747 "parser.tab.c"
    break;

  case 104: /* thf_formula_list: thf_logic_formula comma_thf_logic_formula_list  */
#line 686 "parser.y"
                                                 { (yyval.data) = Tptp_mk_ThfFormulaList_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 4753 "parser.tab.c"
    break;

  case 105: /* comma_thf_logic_formula_list: %empty  */
#line 690 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 4759 "parser.tab.c"
    break;

  case 106: /* comma_thf_logic_formula_list: comma_thf_logic_formula_list comma_thf_logic_formula  */
#line 691 "parser.y"
                                                         { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 4765 "parser.tab.c"
    break;

  case 107: /* comma_thf_logic_formula: "," thf_logic_formula  */
#line 695 "parser.y"
                        { (yyval.data) = Tptp_mk_CommaThfLogicFormula_mk((yyvsp[0].data)); }
#line 4771 "parser.tab.c"
    break;

  case 108: /* thf_atom_typing: untyped_atom ":" thf_top_level_type  */
#line 699 "parser.y"
                                      { (yyval.data) = Tptp_mk_ThfAtomTyping_untypedAtomThfTopLevelType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4777 "parser.tab.c"
    break;

  case 109: /* thf_atom_typing: "(" thf_atom_typing ")"  */
#line 700 "parser.y"
                            { (yyval.data) = Tptp_mk_ThfAtomTyping_thfAtomTyping((yyvsp[-1].data)); }
#line 4783 "parser.tab.c"
    break;

  case 110: /* thf_top_level_type: thf_unitary_type  */
#line 704 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfTopLevelType_thfUnitaryType((yyvsp[0].data)); }
#line 4789 "parser.tab.c"
    break;

  case 111: /* thf_top_level_type: thf_mapping_type  */
#line 705 "parser.y"
                     { (yyval.data) = Tptp_mk_ThfTopLevelType_thfMappingType((yyvsp[0].data)); }
#line 4795 "parser.tab.c"
    break;

  case 112: /* thf_top_level_type: thf_apply_type  */
#line 706 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfTopLevelType_thfApplyType((yyvsp[0].data)); }
#line 4801 "parser.tab.c"
    break;

  case 113: /* thf_unitary_type: thf_unitary_formula  */
#line 710 "parser.y"
                      { (yyval.data) = Tptp_mk_ThfUnitaryType_mk((yyvsp[0].data)); }
#line 4807 "parser.tab.c"
    break;

  case 114: /* thf_apply_type: thf_apply_formula  */
#line 714 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfApplyType_mk((yyvsp[0].data)); }
#line 4813 "parser.tab.c"
    break;

  case 115: /* thf_binary_type: thf_mapping_type  */
#line 718 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfBinaryType_thfMappingType((yyvsp[0].data)); }
#line 4819 "parser.tab.c"
    break;

  case 116: /* thf_binary_type: thf_xprod_type  */
#line 719 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfBinaryType_thfXprodType((yyvsp[0].data)); }
#line 4825 "parser.tab.c"
    break;

  case 117: /* thf_binary_type: thf_union_type  */
#line 720 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfBinaryType_thfUnionType((yyvsp[0].data)); }
#line 4831 "parser.tab.c"
    break;

  case 118: /* thf_mapping_type: thf_unitary_type ">" thf_unitary_type  */
#line 724 "parser.y"
                                          { (yyval.data) = Tptp_mk_ThfMappingType_thfUnitaryTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4837 "parser.tab.c"
    break;

  case 119: /* thf_mapping_type: thf_unitary_type ">" thf_mapping_type  */
#line 725 "parser.y"
                                            { (yyval.data) = Tptp_mk_ThfMappingType_thfUnitaryTypeThfMappingType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4843 "parser.tab.c"
    break;

  case 120: /* thf_xprod_type: thf_unitary_type "*" thf_unitary_type  */
#line 729 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfXprodType_thfUnitaryTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4849 "parser.tab.c"
    break;

  case 121: /* thf_xprod_type: thf_xprod_type "*" thf_unitary_type  */
#line 730 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfXprodType_thfXprodTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4855 "parser.tab.c"
    break;

  case 122: /* thf_union_type: thf_unitary_type "+" thf_unitary_type  */
#line 734 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfUnionType_thfUnitaryTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4861 "parser.tab.c"
    break;

  case 123: /* thf_union_type: thf_union_type "+" thf_unitary_type  */
#line 735 "parser.y"
                                         { (yyval.data) = Tptp_mk_ThfUnionType_thfUnionTypeThfUnitaryType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4867 "parser.tab.c"
    break;

  case 124: /* thf_subtype: untyped_atom subtype_sign atom  */
#line 739 "parser.y"
                                 { (yyval.data) = Tptp_mk_ThfSubtype_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4873 "parser.tab.c"
    break;

  case 125: /* thf_definition: thf_atomic_formula identical thf_logic_formula  */
#line 743 "parser.y"
                                                 { (yyval.data) = Tptp_mk_ThfDefinition_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4879 "parser.tab.c"
    break;

  case 126: /* thf_sequent: thf_tuple gentzen_arrow thf_tuple  */
#line 747 "parser.y"
                                    { (yyval.data) = Tptp_mk_ThfSequent_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4885 "parser.tab.c"
    break;

  case 127: /* tff_formula: tff_logic_formula  */
#line 751 "parser.y"
                    { (yyval.data) = Tptp_mk_TffFormula_tffLogicFormula((yyvsp[0].data)); }
#line 4891 "parser.tab.c"
    break;

  case 128: /* tff_formula: tff_atom_typing  */
#line 752 "parser.y"
                    { (yyval.data) = Tptp_mk_TffFormula_tffAtomTyping((yyvsp[0].data)); }
#line 4897 "parser.tab.c"
    break;

  case 129: /* tff_formula: tff_subtype  */
#line 753 "parser.y"
                { (yyval.data) = Tptp_mk_TffFormula_tffSubtype((yyvsp[0].data)); }
#line 4903 "parser.tab.c"
    break;

  case 130: /* tff_logic_formula: tff_unitary_formula  */
#line 757 "parser.y"
                      { (yyval.data) = Tptp_mk_TffLogicFormula_tffUnitaryFormula((yyvsp[0].data)); }
#line 4909 "parser.tab.c"
    break;

  case 131: /* tff_logic_formula: tff_unary_formula  */
#line 758 "parser.y"
                      { (yyval.data) = Tptp_mk_TffLogicFormula_tffUnaryFormula((yyvsp[0].data)); }
#line 4915 "parser.tab.c"
    break;

  case 132: /* tff_logic_formula: tff_binary_formula  */
#line 759 "parser.y"
                       { (yyval.data) = Tptp_mk_TffLogicFormula_tffBinaryFormula((yyvsp[0].data)); }
#line 4921 "parser.tab.c"
    break;

  case 133: /* tff_logic_formula: tff_defined_infix  */
#line 760 "parser.y"
                      { (yyval.data) = Tptp_mk_TffLogicFormula_tffDefinedInfix((yyvsp[0].data)); }
#line 4927 "parser.tab.c"
    break;

  case 134: /* tff_logic_formula: txf_definition  */
#line 761 "parser.y"
                   { (yyval.data) = Tptp_mk_TffLogicFormula_txfDefinition((yyvsp[0].data)); }
#line 4933 "parser.tab.c"
    break;

  case 135: /* tff_logic_formula: txf_sequent  */
#line 762 "parser.y"
                { (yyval.data) = Tptp_mk_TffLogicFormula_txfSequent((yyvsp[0].data)); }
#line 4939 "parser.tab.c"
    break;

  case 136: /* tff_binary_formula: tff_binary_nonassoc  */
#line 766 "parser.y"
                      { (yyval.data) = Tptp_mk_TffBinaryFormula_tffBinaryNonassoc((yyvsp[0].data)); }
#line 4945 "parser.tab.c"
    break;

  case 137: /* tff_binary_formula: tff_binary_assoc  */
#line 767 "parser.y"
                     { (yyval.data) = Tptp_mk_TffBinaryFormula_tffBinaryAssoc((yyvsp[0].data)); }
#line 4951 "parser.tab.c"
    break;

  case 138: /* tff_binary_nonassoc: tff_unit_formula nonassoc_connective tff_unit_formula  */
#line 771 "parser.y"
                                                        { (yyval.data) = Tptp_mk_TffBinaryNonassoc_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 4957 "parser.tab.c"
    break;

  case 139: /* tff_binary_assoc: tff_or_formula  */
#line 775 "parser.y"
                 { (yyval.data) = Tptp_mk_TffBinaryAssoc_tffOrFormula((yyvsp[0].data)); }
#line 4963 "parser.tab.c"
    break;

  case 140: /* tff_binary_assoc: tff_and_formula  */
#line 776 "parser.y"
                    { (yyval.data) = Tptp_mk_TffBinaryAssoc_tffAndFormula((yyvsp[0].data)); }
#line 4969 "parser.tab.c"
    break;

  case 141: /* tff_or_formula: tff_unit_formula "|" tff_unit_formula  */
#line 780 "parser.y"
                                          { (yyval.data) = Tptp_mk_TffOrFormula_tffUnitFormulaTffUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4975 "parser.tab.c"
    break;

  case 142: /* tff_or_formula: tff_or_formula "|" tff_unit_formula  */
#line 781 "parser.y"
                                          { (yyval.data) = Tptp_mk_TffOrFormula_tffOrFormulaTffUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4981 "parser.tab.c"
    break;

  case 143: /* tff_and_formula: tff_unit_formula "&" tff_unit_formula  */
#line 785 "parser.y"
                                        { (yyval.data) = Tptp_mk_TffAndFormula_tffUnitFormulaTffUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4987 "parser.tab.c"
    break;

  case 144: /* tff_and_formula: tff_and_formula "&" tff_unit_formula  */
#line 786 "parser.y"
                                         { (yyval.data) = Tptp_mk_TffAndFormula_tffAndFormulaTffUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 4993 "parser.tab.c"
    break;

  case 145: /* tff_unit_formula: tff_unitary_formula  */
#line 790 "parser.y"
                      { (yyval.data) = Tptp_mk_TffUnitFormula_tffUnitaryFormula((yyvsp[0].data)); }
#line 4999 "parser.tab.c"
    break;

  case 146: /* tff_unit_formula: tff_unary_formula  */
#line 791 "parser.y"
                      { (yyval.data) = Tptp_mk_TffUnitFormula_tffUnaryFormula((yyvsp[0].data)); }
#line 5005 "parser.tab.c"
    break;

  case 147: /* tff_unit_formula: tff_defined_infix  */
#line 792 "parser.y"
                      { (yyval.data) = Tptp_mk_TffUnitFormula_tffDefinedInfix((yyvsp[0].data)); }
#line 5011 "parser.tab.c"
    break;

  case 148: /* tff_preunit_formula: tff_unitary_formula  */
#line 796 "parser.y"
                      { (yyval.data) = Tptp_mk_TffPreunitFormula_tffUnitaryFormula((yyvsp[0].data)); }
#line 5017 "parser.tab.c"
    break;

  case 149: /* tff_preunit_formula: tff_prefix_unary  */
#line 797 "parser.y"
                     { (yyval.data) = Tptp_mk_TffPreunitFormula_tffPrefixUnary((yyvsp[0].data)); }
#line 5023 "parser.tab.c"
    break;

  case 150: /* tff_unitary_formula: tff_quantified_formula  */
#line 801 "parser.y"
                         { (yyval.data) = Tptp_mk_TffUnitaryFormula_tffQuantifiedFormula((yyvsp[0].data)); }
#line 5029 "parser.tab.c"
    break;

  case 151: /* tff_unitary_formula: tff_atomic_formula  */
#line 802 "parser.y"
                       { (yyval.data) = Tptp_mk_TffUnitaryFormula_tffAtomicFormula((yyvsp[0].data)); }
#line 5035 "parser.tab.c"
    break;

  case 152: /* tff_unitary_formula: txf_unitary_formula  */
#line 803 "parser.y"
                        { (yyval.data) = Tptp_mk_TffUnitaryFormula_txfUnitaryFormula((yyvsp[0].data)); }
#line 5041 "parser.tab.c"
    break;

  case 153: /* tff_unitary_formula: "(" tff_logic_formula ")"  */
#line 804 "parser.y"
                              { (yyval.data) = Tptp_mk_TffUnitaryFormula_tffLogicFormula((yyvsp[-1].data)); }
#line 5047 "parser.tab.c"
    break;

  case 154: /* txf_unitary_formula: variable  */
#line 808 "parser.y"
           { (yyval.data) = Tptp_mk_TxfUnitaryFormula_mk((yyvsp[0].data)); }
#line 5053 "parser.tab.c"
    break;

  case 155: /* tff_quantified_formula: tff_quantifier "[" tff_variable_list "]" ":" tff_unit_formula  */
#line 812 "parser.y"
                                                                { (yyval.data) = Tptp_mk_TffQuantifiedFormula_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[0].data)); }
#line 5059 "parser.tab.c"
    break;

  case 156: /* tff_variable_list: tff_variable  */
#line 816 "parser.y"
               { (yyval.data) = Tptp_mk_TffVariableList_tffVariable((yyvsp[0].data)); }
#line 5065 "parser.tab.c"
    break;

  case 157: /* tff_variable_list: tff_variable "," tff_variable_list  */
#line 817 "parser.y"
                                       { (yyval.data) = Tptp_mk_TffVariableList_tffVariableTffVariableList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5071 "parser.tab.c"
    break;

  case 158: /* tff_variable: tff_typed_variable  */
#line 821 "parser.y"
                     { (yyval.data) = Tptp_mk_TffVariable_tffTypedVariable((yyvsp[0].data)); }
#line 5077 "parser.tab.c"
    break;

  case 159: /* tff_variable: variable  */
#line 822 "parser.y"
             { (yyval.data) = Tptp_mk_TffVariable_variable((yyvsp[0].data)); }
#line 5083 "parser.tab.c"
    break;

  case 160: /* tff_typed_variable: variable ":" tff_atomic_type  */
#line 826 "parser.y"
                               { (yyval.data) = Tptp_mk_TffTypedVariable_mk((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5089 "parser.tab.c"
    break;

  case 161: /* tff_unary_formula: tff_prefix_unary  */
#line 830 "parser.y"
                   { (yyval.data) = Tptp_mk_TffUnaryFormula_tffPrefixUnary((yyvsp[0].data)); }
#line 5095 "parser.tab.c"
    break;

  case 162: /* tff_unary_formula: tff_infix_unary  */
#line 831 "parser.y"
                    { (yyval.data) = Tptp_mk_TffUnaryFormula_tffInfixUnary((yyvsp[0].data)); }
#line 5101 "parser.tab.c"
    break;

  case 163: /* tff_prefix_unary: tff_unary_connective tff_preunit_formula  */
#line 835 "parser.y"
                                           { (yyval.data) = Tptp_mk_TffPrefixUnary_mk((yyvsp[-1].data), (yyvsp[0].data)); }
#line 5107 "parser.tab.c"
    break;

  case 164: /* tff_infix_unary: tff_unitary_term infix_inequality tff_unitary_term  */
#line 839 "parser.y"
                                                     { (yyval.data) = Tptp_mk_TffInfixUnary_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5113 "parser.tab.c"
    break;

  case 165: /* tff_atomic_formula: tff_plain_atomic  */
#line 843 "parser.y"
                   { (yyval.data) = Tptp_mk_TffAtomicFormula_tffPlainAtomic((yyvsp[0].data)); }
#line 5119 "parser.tab.c"
    break;

  case 166: /* tff_atomic_formula: tff_defined_atomic  */
#line 844 "parser.y"
                       { (yyval.data) = Tptp_mk_TffAtomicFormula_tffDefinedAtomic((yyvsp[0].data)); }
#line 5125 "parser.tab.c"
    break;

  case 167: /* tff_atomic_formula: tff_system_atomic  */
#line 845 "parser.y"
                      { (yyval.data) = Tptp_mk_TffAtomicFormula_tffSystemAtomic((yyvsp[0].data)); }
#line 5131 "parser.tab.c"
    break;

  case 168: /* tff_plain_atomic: constant  */
#line 849 "parser.y"
           { (yyval.data) = Tptp_mk_TffPlainAtomic_constant((yyvsp[0].data)); }
#line 5137 "parser.tab.c"
    break;

  case 169: /* tff_plain_atomic: functor "(" tff_arguments ")"  */
#line 850 "parser.y"
                                  { (yyval.data) = Tptp_mk_TffPlainAtomic_functorTffArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5143 "parser.tab.c"
    break;

  case 170: /* tff_defined_atomic: tff_defined_plain  */
#line 854 "parser.y"
                    { (yyval.data) = Tptp_mk_TffDefinedAtomic_mk((yyvsp[0].data)); }
#line 5149 "parser.tab.c"
    break;

  case 171: /* tff_defined_plain: defined_constant  */
#line 858 "parser.y"
                   { (yyval.data) = Tptp_mk_TffDefinedPlain_definedConstant((yyvsp[0].data)); }
#line 5155 "parser.tab.c"
    break;

  case 172: /* tff_defined_plain: defined_functor "(" tff_arguments ")"  */
#line 859 "parser.y"
                                          { (yyval.data) = Tptp_mk_TffDefinedPlain_definedFunctorTffArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5161 "parser.tab.c"
    break;

  case 173: /* tff_defined_plain: nxf_atom  */
#line 860 "parser.y"
             { (yyval.data) = Tptp_mk_TffDefinedPlain_nxfAtom((yyvsp[0].data)); }
#line 5167 "parser.tab.c"
    break;

  case 174: /* tff_defined_plain: txf_let  */
#line 861 "parser.y"
            { (yyval.data) = Tptp_mk_TffDefinedPlain_txfLet((yyvsp[0].data)); }
#line 5173 "parser.tab.c"
    break;

  case 175: /* tff_defined_infix: tff_unitary_term defined_infix_pred tff_unitary_term  */
#line 865 "parser.y"
                                                       { (yyval.data) = Tptp_mk_TffDefinedInfix_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5179 "parser.tab.c"
    break;

  case 176: /* tff_system_atomic: system_constant  */
#line 869 "parser.y"
                  { (yyval.data) = Tptp_mk_TffSystemAtomic_systemConstant((yyvsp[0].data)); }
#line 5185 "parser.tab.c"
    break;

  case 177: /* tff_system_atomic: system_functor "(" tff_arguments ")"  */
#line 870 "parser.y"
                                         { (yyval.data) = Tptp_mk_TffSystemAtomic_systemFunctorTffArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5191 "parser.tab.c"
    break;

  case 178: /* txf_let: "$let(" txf_let_types "," txf_let_defns "," tff_term ")"  */
#line 874 "parser.y"
                                                           { (yyval.data) = Tptp_mk_TxfLet_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5197 "parser.tab.c"
    break;

  case 179: /* txf_let_types: tff_atom_typing  */
#line 878 "parser.y"
                  { (yyval.data) = Tptp_mk_TxfLetTypes_tffAtomTyping((yyvsp[0].data)); }
#line 5203 "parser.tab.c"
    break;

  case 180: /* txf_let_types: "[" tff_atom_typing_list "]"  */
#line 879 "parser.y"
                                 { (yyval.data) = Tptp_mk_TxfLetTypes_tffAtomTypingList((yyvsp[-1].data)); }
#line 5209 "parser.tab.c"
    break;

  case 181: /* tff_atom_typing_list: tff_atom_typing  */
#line 883 "parser.y"
                  { (yyval.data) = Tptp_mk_TffAtomTypingList_tffAtomTyping((yyvsp[0].data)); }
#line 5215 "parser.tab.c"
    break;

  case 182: /* tff_atom_typing_list: tff_atom_typing "," tff_atom_typing_list  */
#line 884 "parser.y"
                                             { (yyval.data) = Tptp_mk_TffAtomTypingList_tffAtomTypingTffAtomTypingList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5221 "parser.tab.c"
    break;

  case 183: /* txf_let_defns: txf_let_defn  */
#line 888 "parser.y"
               { (yyval.data) = Tptp_mk_TxfLetDefns_txfLetDefn((yyvsp[0].data)); }
#line 5227 "parser.tab.c"
    break;

  case 184: /* txf_let_defns: "[" txf_let_defn_list "]"  */
#line 889 "parser.y"
                              { (yyval.data) = Tptp_mk_TxfLetDefns_txfLetDefnList((yyvsp[-1].data)); }
#line 5233 "parser.tab.c"
    break;

  case 185: /* txf_let_defn: txf_let_LHS assignment tff_term  */
#line 893 "parser.y"
                                  { (yyval.data) = Tptp_mk_TxfLetDefn_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5239 "parser.tab.c"
    break;

  case 186: /* txf_let_LHS: tff_plain_atomic  */
#line 897 "parser.y"
                   { (yyval.data) = Tptp_mk_TxfLetLHS_tffPlainAtomic((yyvsp[0].data)); }
#line 5245 "parser.tab.c"
    break;

  case 187: /* txf_let_LHS: txf_tuple  */
#line 898 "parser.y"
              { (yyval.data) = Tptp_mk_TxfLetLHS_txfTuple((yyvsp[0].data)); }
#line 5251 "parser.tab.c"
    break;

  case 188: /* txf_let_defn_list: txf_let_defn  */
#line 902 "parser.y"
               { (yyval.data) = Tptp_mk_TxfLetDefnList_txfLetDefn((yyvsp[0].data)); }
#line 5257 "parser.tab.c"
    break;

  case 189: /* txf_let_defn_list: txf_let_defn "," txf_let_defn_list  */
#line 903 "parser.y"
                                       { (yyval.data) = Tptp_mk_TxfLetDefnList_txfLetDefnTxfLetDefnList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5263 "parser.tab.c"
    break;

  case 190: /* nxf_atom: nxf_long_connective "@" "(" tff_arguments ")"  */
#line 907 "parser.y"
                                                { (yyval.data) = Tptp_mk_NxfAtom_mk((yyvsp[-4].data), (yyvsp[-1].data)); }
#line 5269 "parser.tab.c"
    break;

  case 191: /* tff_term: tff_logic_formula  */
#line 911 "parser.y"
                    { (yyval.data) = Tptp_mk_TffTerm_tffLogicFormula((yyvsp[0].data)); }
#line 5275 "parser.tab.c"
    break;

  case 192: /* tff_term: defined_term  */
#line 912 "parser.y"
                 { (yyval.data) = Tptp_mk_TffTerm_definedTerm((yyvsp[0].data)); }
#line 5281 "parser.tab.c"
    break;

  case 193: /* tff_term: txf_tuple  */
#line 913 "parser.y"
              { (yyval.data) = Tptp_mk_TffTerm_txfTuple((yyvsp[0].data)); }
#line 5287 "parser.tab.c"
    break;

  case 194: /* tff_unitary_term: tff_atomic_formula  */
#line 917 "parser.y"
                     { (yyval.data) = Tptp_mk_TffUnitaryTerm_tffAtomicFormula((yyvsp[0].data)); }
#line 5293 "parser.tab.c"
    break;

  case 195: /* tff_unitary_term: defined_term  */
#line 918 "parser.y"
                 { (yyval.data) = Tptp_mk_TffUnitaryTerm_definedTerm((yyvsp[0].data)); }
#line 5299 "parser.tab.c"
    break;

  case 196: /* tff_unitary_term: txf_tuple  */
#line 919 "parser.y"
              { (yyval.data) = Tptp_mk_TffUnitaryTerm_txfTuple((yyvsp[0].data)); }
#line 5305 "parser.tab.c"
    break;

  case 197: /* tff_unitary_term: variable  */
#line 920 "parser.y"
             { (yyval.data) = Tptp_mk_TffUnitaryTerm_variable((yyvsp[0].data)); }
#line 5311 "parser.tab.c"
    break;

  case 198: /* tff_unitary_term: "(" tff_logic_formula ")"  */
#line 921 "parser.y"
                              { (yyval.data) = Tptp_mk_TffUnitaryTerm_tffLogicFormula((yyvsp[-1].data)); }
#line 5317 "parser.tab.c"
    break;

  case 199: /* txf_tuple: "[]"  */
#line 925 "parser.y"
       { (yyval.data) = Tptp_mk_TxfTuple_empty; }
#line 5323 "parser.tab.c"
    break;

  case 200: /* txf_tuple: "[" tff_arguments "]"  */
#line 926 "parser.y"
                          { (yyval.data) = Tptp_mk_TxfTuple_tffArguments((yyvsp[-1].data)); }
#line 5329 "parser.tab.c"
    break;

  case 201: /* tff_arguments: tff_term comma_tff_term_list  */
#line 930 "parser.y"
                               { (yyval.data) = Tptp_mk_TffArguments_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 5335 "parser.tab.c"
    break;

  case 202: /* comma_tff_term_list: %empty  */
#line 934 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 5341 "parser.tab.c"
    break;

  case 203: /* comma_tff_term_list: comma_tff_term_list comma_tff_term  */
#line 935 "parser.y"
                                       { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 5347 "parser.tab.c"
    break;

  case 204: /* comma_tff_term: "," tff_term  */
#line 939 "parser.y"
               { (yyval.data) = Tptp_mk_CommaTffTerm_mk((yyvsp[0].data)); }
#line 5353 "parser.tab.c"
    break;

  case 205: /* tff_atom_typing: untyped_atom ":" tff_top_level_type  */
#line 943 "parser.y"
                                      { (yyval.data) = Tptp_mk_TffAtomTyping_untypedAtomTffTopLevelType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5359 "parser.tab.c"
    break;

  case 206: /* tff_atom_typing: "(" tff_atom_typing ")"  */
#line 944 "parser.y"
                            { (yyval.data) = Tptp_mk_TffAtomTyping_tffAtomTyping((yyvsp[-1].data)); }
#line 5365 "parser.tab.c"
    break;

  case 207: /* tff_top_level_type: tff_atomic_type  */
#line 948 "parser.y"
                  { (yyval.data) = Tptp_mk_TffTopLevelType_tffAtomicType((yyvsp[0].data)); }
#line 5371 "parser.tab.c"
    break;

  case 208: /* tff_top_level_type: tff_non_atomic_type  */
#line 949 "parser.y"
                        { (yyval.data) = Tptp_mk_TffTopLevelType_tffNonAtomicType((yyvsp[0].data)); }
#line 5377 "parser.tab.c"
    break;

  case 209: /* tff_non_atomic_type: tff_mapping_type  */
#line 953 "parser.y"
                   { (yyval.data) = Tptp_mk_TffNonAtomicType_tffMappingType((yyvsp[0].data)); }
#line 5383 "parser.tab.c"
    break;

  case 210: /* tff_non_atomic_type: tf1_quantified_type  */
#line 954 "parser.y"
                        { (yyval.data) = Tptp_mk_TffNonAtomicType_tf1QuantifiedType((yyvsp[0].data)); }
#line 5389 "parser.tab.c"
    break;

  case 211: /* tff_non_atomic_type: "(" tff_non_atomic_type ")"  */
#line 955 "parser.y"
                                { (yyval.data) = Tptp_mk_TffNonAtomicType_tffNonAtomicType((yyvsp[-1].data)); }
#line 5395 "parser.tab.c"
    break;

  case 212: /* tf1_quantified_type: type_quantifier "[" tff_variable_list "]" ":" tff_monotype  */
#line 959 "parser.y"
                                                             { (yyval.data) = Tptp_mk_Tf1QuantifiedType_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[0].data)); }
#line 5401 "parser.tab.c"
    break;

  case 213: /* tff_monotype: tff_atomic_type  */
#line 963 "parser.y"
                  { (yyval.data) = Tptp_mk_TffMonotype_tffAtomicType((yyvsp[0].data)); }
#line 5407 "parser.tab.c"
    break;

  case 214: /* tff_monotype: "(" tff_mapping_type ")"  */
#line 964 "parser.y"
                             { (yyval.data) = Tptp_mk_TffMonotype_tffMappingType((yyvsp[-1].data)); }
#line 5413 "parser.tab.c"
    break;

  case 215: /* tff_monotype: tf1_quantified_type  */
#line 965 "parser.y"
                        { (yyval.data) = Tptp_mk_TffMonotype_tf1QuantifiedType((yyvsp[0].data)); }
#line 5419 "parser.tab.c"
    break;

  case 216: /* tff_unitary_type: tff_atomic_type  */
#line 969 "parser.y"
                  { (yyval.data) = Tptp_mk_TffUnitaryType_tffAtomicType((yyvsp[0].data)); }
#line 5425 "parser.tab.c"
    break;

  case 217: /* tff_unitary_type: "(" tff_xprod_type ")"  */
#line 970 "parser.y"
                           { (yyval.data) = Tptp_mk_TffUnitaryType_tffXprodType((yyvsp[-1].data)); }
#line 5431 "parser.tab.c"
    break;

  case 218: /* tff_atomic_type: type_constant  */
#line 974 "parser.y"
                { (yyval.data) = Tptp_mk_TffAtomicType_typeConstant((yyvsp[0].data)); }
#line 5437 "parser.tab.c"
    break;

  case 219: /* tff_atomic_type: defined_type  */
#line 975 "parser.y"
                 { (yyval.data) = Tptp_mk_TffAtomicType_definedType((yyvsp[0].data)); }
#line 5443 "parser.tab.c"
    break;

  case 220: /* tff_atomic_type: variable  */
#line 976 "parser.y"
             { (yyval.data) = Tptp_mk_TffAtomicType_variable((yyvsp[0].data)); }
#line 5449 "parser.tab.c"
    break;

  case 221: /* tff_atomic_type: type_functor "(" tff_type_arguments ")"  */
#line 977 "parser.y"
                                            { (yyval.data) = Tptp_mk_TffAtomicType_typeFunctorTffTypeArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5455 "parser.tab.c"
    break;

  case 222: /* tff_atomic_type: "(" tff_atomic_type ")"  */
#line 978 "parser.y"
                            { (yyval.data) = Tptp_mk_TffAtomicType_tffAtomicType((yyvsp[-1].data)); }
#line 5461 "parser.tab.c"
    break;

  case 223: /* tff_atomic_type: txf_tuple_type  */
#line 979 "parser.y"
                   { (yyval.data) = Tptp_mk_TffAtomicType_txfTupleType((yyvsp[0].data)); }
#line 5467 "parser.tab.c"
    break;

  case 224: /* tff_type_arguments: tff_atomic_type  */
#line 983 "parser.y"
                  { (yyval.data) = Tptp_mk_TffTypeArguments_tffAtomicType((yyvsp[0].data)); }
#line 5473 "parser.tab.c"
    break;

  case 225: /* tff_type_arguments: tff_atomic_type "," tff_type_arguments  */
#line 984 "parser.y"
                                           { (yyval.data) = Tptp_mk_TffTypeArguments_tffAtomicTypeTffTypeArguments((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5479 "parser.tab.c"
    break;

  case 226: /* tff_mapping_type: tff_unitary_type ">" tff_atomic_type  */
#line 988 "parser.y"
                                         { (yyval.data) = Tptp_mk_TffMappingType_mk((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5485 "parser.tab.c"
    break;

  case 227: /* tff_xprod_type: tff_unitary_type "*" tff_atomic_type  */
#line 992 "parser.y"
                                        { (yyval.data) = Tptp_mk_TffXprodType_tffUnitaryTypeTffAtomicType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5491 "parser.tab.c"
    break;

  case 228: /* tff_xprod_type: tff_xprod_type "*" tff_atomic_type  */
#line 993 "parser.y"
                                        { (yyval.data) = Tptp_mk_TffXprodType_tffXprodTypeTffAtomicType((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5497 "parser.tab.c"
    break;

  case 229: /* txf_tuple_type: "[" tff_type_list "]"  */
#line 997 "parser.y"
                        { (yyval.data) = Tptp_mk_TxfTupleType_mk((yyvsp[-1].data)); }
#line 5503 "parser.tab.c"
    break;

  case 230: /* tff_type_list: tff_top_level_type  */
#line 1001 "parser.y"
                     { (yyval.data) = Tptp_mk_TffTypeList_tffTopLevelType((yyvsp[0].data)); }
#line 5509 "parser.tab.c"
    break;

  case 231: /* tff_type_list: tff_top_level_type "," tff_type_list  */
#line 1002 "parser.y"
                                         { (yyval.data) = Tptp_mk_TffTypeList_tffTopLevelTypeTffTypeList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5515 "parser.tab.c"
    break;

  case 232: /* tff_subtype: untyped_atom subtype_sign atom  */
#line 1006 "parser.y"
                                 { (yyval.data) = Tptp_mk_TffSubtype_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5521 "parser.tab.c"
    break;

  case 233: /* txf_definition: tff_atomic_formula identical tff_term  */
#line 1010 "parser.y"
                                        { (yyval.data) = Tptp_mk_TxfDefinition_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5527 "parser.tab.c"
    break;

  case 234: /* txf_sequent: txf_tuple gentzen_arrow txf_tuple  */
#line 1014 "parser.y"
                                    { (yyval.data) = Tptp_mk_TxfSequent_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5533 "parser.tab.c"
    break;

  case 235: /* nhf_long_connective: "{" ntf_connective_name "}"  */
#line 1018 "parser.y"
                              { (yyval.data) = Tptp_mk_NhfLongConnective_ntfConnectiveName((yyvsp[-1].data)); }
#line 5539 "parser.tab.c"
    break;

  case 236: /* nhf_long_connective: "{" ntf_connective_name "(" nhf_parameter_list ")}"  */
#line 1019 "parser.y"
                                                        { (yyval.data) = Tptp_mk_NhfLongConnective_ntfConnectiveNameNhfParameterList((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5545 "parser.tab.c"
    break;

  case 237: /* nhf_parameter_list: nhf_parameter  */
#line 1023 "parser.y"
                { (yyval.data) = Tptp_mk_NhfParameterList_nhfParameter((yyvsp[0].data)); }
#line 5551 "parser.tab.c"
    break;

  case 238: /* nhf_parameter_list: nhf_parameter "," nhf_parameter_list  */
#line 1024 "parser.y"
                                         { (yyval.data) = Tptp_mk_NhfParameterList_nhfParameterNhfParameterList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5557 "parser.tab.c"
    break;

  case 239: /* nhf_parameter: ntf_index  */
#line 1028 "parser.y"
            { (yyval.data) = Tptp_mk_NhfParameter_ntfIndex((yyvsp[0].data)); }
#line 5563 "parser.tab.c"
    break;

  case 240: /* nhf_parameter: nhf_key_pair  */
#line 1029 "parser.y"
                 { (yyval.data) = Tptp_mk_NhfParameter_nhfKeyPair((yyvsp[0].data)); }
#line 5569 "parser.tab.c"
    break;

  case 241: /* nhf_key_pair: thf_definition  */
#line 1033 "parser.y"
                 { (yyval.data) = Tptp_mk_NhfKeyPair_mk((yyvsp[0].data)); }
#line 5575 "parser.tab.c"
    break;

  case 242: /* nxf_long_connective: "{" ntf_connective_name "}"  */
#line 1037 "parser.y"
                              { (yyval.data) = Tptp_mk_NxfLongConnective_ntfConnectiveName((yyvsp[-1].data)); }
#line 5581 "parser.tab.c"
    break;

  case 243: /* nxf_long_connective: "{" ntf_connective_name "(" nxf_parameter_list ")}"  */
#line 1038 "parser.y"
                                                        { (yyval.data) = Tptp_mk_NxfLongConnective_ntfConnectiveNameNxfParameterList((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5587 "parser.tab.c"
    break;

  case 244: /* nxf_parameter_list: nxf_parameter  */
#line 1042 "parser.y"
                { (yyval.data) = Tptp_mk_NxfParameterList_nxfParameter((yyvsp[0].data)); }
#line 5593 "parser.tab.c"
    break;

  case 245: /* nxf_parameter_list: nxf_parameter "," nxf_parameter_list  */
#line 1043 "parser.y"
                                         { (yyval.data) = Tptp_mk_NxfParameterList_nxfParameterNxfParameterList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5599 "parser.tab.c"
    break;

  case 246: /* nxf_parameter: ntf_index  */
#line 1047 "parser.y"
            { (yyval.data) = Tptp_mk_NxfParameter_ntfIndex((yyvsp[0].data)); }
#line 5605 "parser.tab.c"
    break;

  case 247: /* nxf_parameter: nxf_key_pair  */
#line 1048 "parser.y"
                 { (yyval.data) = Tptp_mk_NxfParameter_nxfKeyPair((yyvsp[0].data)); }
#line 5611 "parser.tab.c"
    break;

  case 248: /* nxf_key_pair: txf_definition  */
#line 1052 "parser.y"
                 { (yyval.data) = Tptp_mk_NxfKeyPair_mk((yyvsp[0].data)); }
#line 5617 "parser.tab.c"
    break;

  case 249: /* ntf_connective_name: def_or_sys_constant  */
#line 1056 "parser.y"
                      { (yyval.data) = Tptp_mk_NtfConnectiveName_mk((yyvsp[0].data)); }
#line 5623 "parser.tab.c"
    break;

  case 250: /* ntf_index: "#" tff_unitary_term  */
#line 1060 "parser.y"
                        { (yyval.data) = Tptp_mk_NtfIndex_mk((yyvsp[0].data)); }
#line 5629 "parser.tab.c"
    break;

  case 251: /* ntf_short_connective: "[.]"  */
#line 1064 "parser.y"
        { (yyval.data) = Tptp_mk_NtfShortConnective_bracket; }
#line 5635 "parser.tab.c"
    break;

  case 252: /* ntf_short_connective: "<" "." ">"  */
#line 1065 "parser.y"
                        { (yyval.data) = Tptp_mk_NtfShortConnective_angle; }
#line 5641 "parser.tab.c"
    break;

  case 253: /* ntf_short_connective: "{.}"  */
#line 1066 "parser.y"
          { (yyval.data) = Tptp_mk_NtfShortConnective_brace; }
#line 5647 "parser.tab.c"
    break;

  case 254: /* ntf_short_connective: "(.)"  */
#line 1067 "parser.y"
          { (yyval.data) = Tptp_mk_NtfShortConnective_parens; }
#line 5653 "parser.tab.c"
    break;

  case 255: /* tcf_formula: tcf_logic_formula  */
#line 1071 "parser.y"
                    { (yyval.data) = Tptp_mk_TcfFormula_tcfLogicFormula((yyvsp[0].data)); }
#line 5659 "parser.tab.c"
    break;

  case 256: /* tcf_formula: tff_atom_typing  */
#line 1072 "parser.y"
                    { (yyval.data) = Tptp_mk_TcfFormula_tffAtomTyping((yyvsp[0].data)); }
#line 5665 "parser.tab.c"
    break;

  case 257: /* tcf_logic_formula: tcf_quantified_formula  */
#line 1076 "parser.y"
                         { (yyval.data) = Tptp_mk_TcfLogicFormula_tcfQuantifiedFormula((yyvsp[0].data)); }
#line 5671 "parser.tab.c"
    break;

  case 258: /* tcf_logic_formula: cnf_formula  */
#line 1077 "parser.y"
                { (yyval.data) = Tptp_mk_TcfLogicFormula_cnfFormula((yyvsp[0].data)); }
#line 5677 "parser.tab.c"
    break;

  case 259: /* tcf_quantified_formula: "!" "[" tff_variable_list "]" ":" tcf_logic_formula  */
#line 1081 "parser.y"
                                                      { (yyval.data) = Tptp_mk_TcfQuantifiedFormula_mk((yyvsp[-3].data), (yyvsp[0].data)); }
#line 5683 "parser.tab.c"
    break;

  case 260: /* fof_formula: fof_logic_formula  */
#line 1085 "parser.y"
                    { (yyval.data) = Tptp_mk_FofFormula_fofLogicFormula((yyvsp[0].data)); }
#line 5689 "parser.tab.c"
    break;

  case 261: /* fof_formula: fof_sequent  */
#line 1086 "parser.y"
                { (yyval.data) = Tptp_mk_FofFormula_fofSequent((yyvsp[0].data)); }
#line 5695 "parser.tab.c"
    break;

  case 262: /* fof_logic_formula: fof_binary_formula  */
#line 1090 "parser.y"
                     { (yyval.data) = Tptp_mk_FofLogicFormula_fofBinaryFormula((yyvsp[0].data)); }
#line 5701 "parser.tab.c"
    break;

  case 263: /* fof_logic_formula: fof_unary_formula  */
#line 1091 "parser.y"
                      { (yyval.data) = Tptp_mk_FofLogicFormula_fofUnaryFormula((yyvsp[0].data)); }
#line 5707 "parser.tab.c"
    break;

  case 264: /* fof_logic_formula: fof_unitary_formula  */
#line 1092 "parser.y"
                        { (yyval.data) = Tptp_mk_FofLogicFormula_fofUnitaryFormula((yyvsp[0].data)); }
#line 5713 "parser.tab.c"
    break;

  case 265: /* fof_binary_formula: fof_binary_nonassoc  */
#line 1096 "parser.y"
                      { (yyval.data) = Tptp_mk_FofBinaryFormula_fofBinaryNonassoc((yyvsp[0].data)); }
#line 5719 "parser.tab.c"
    break;

  case 266: /* fof_binary_formula: fof_binary_assoc  */
#line 1097 "parser.y"
                     { (yyval.data) = Tptp_mk_FofBinaryFormula_fofBinaryAssoc((yyvsp[0].data)); }
#line 5725 "parser.tab.c"
    break;

  case 267: /* fof_binary_nonassoc: fof_unit_formula nonassoc_connective fof_unit_formula  */
#line 1101 "parser.y"
                                                        { (yyval.data) = Tptp_mk_FofBinaryNonassoc_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5731 "parser.tab.c"
    break;

  case 268: /* fof_binary_assoc: fof_or_formula  */
#line 1105 "parser.y"
                 { (yyval.data) = Tptp_mk_FofBinaryAssoc_fofOrFormula((yyvsp[0].data)); }
#line 5737 "parser.tab.c"
    break;

  case 269: /* fof_binary_assoc: fof_and_formula  */
#line 1106 "parser.y"
                    { (yyval.data) = Tptp_mk_FofBinaryAssoc_fofAndFormula((yyvsp[0].data)); }
#line 5743 "parser.tab.c"
    break;

  case 270: /* fof_or_formula: fof_unit_formula "|" fof_unit_formula  */
#line 1110 "parser.y"
                                          { (yyval.data) = Tptp_mk_FofOrFormula_fofUnitFormulaFofUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5749 "parser.tab.c"
    break;

  case 271: /* fof_or_formula: fof_or_formula "|" fof_unit_formula  */
#line 1111 "parser.y"
                                          { (yyval.data) = Tptp_mk_FofOrFormula_fofOrFormulaFofUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5755 "parser.tab.c"
    break;

  case 272: /* fof_and_formula: fof_unit_formula "&" fof_unit_formula  */
#line 1115 "parser.y"
                                        { (yyval.data) = Tptp_mk_FofAndFormula_fofUnitFormulaFofUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5761 "parser.tab.c"
    break;

  case 273: /* fof_and_formula: fof_and_formula "&" fof_unit_formula  */
#line 1116 "parser.y"
                                         { (yyval.data) = Tptp_mk_FofAndFormula_fofAndFormulaFofUnitFormula((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5767 "parser.tab.c"
    break;

  case 274: /* fof_unary_formula: unary_connective fof_unit_formula  */
#line 1120 "parser.y"
                                    { (yyval.data) = Tptp_mk_FofUnaryFormula_unaryConnectiveFofUnitFormula((yyvsp[-1].data), (yyvsp[0].data)); }
#line 5773 "parser.tab.c"
    break;

  case 275: /* fof_unary_formula: fof_infix_unary  */
#line 1121 "parser.y"
                    { (yyval.data) = Tptp_mk_FofUnaryFormula_fofInfixUnary((yyvsp[0].data)); }
#line 5779 "parser.tab.c"
    break;

  case 276: /* fof_infix_unary: fof_term infix_inequality fof_term  */
#line 1125 "parser.y"
                                     { (yyval.data) = Tptp_mk_FofInfixUnary_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5785 "parser.tab.c"
    break;

  case 277: /* fof_unit_formula: fof_unitary_formula  */
#line 1129 "parser.y"
                      { (yyval.data) = Tptp_mk_FofUnitFormula_fofUnitaryFormula((yyvsp[0].data)); }
#line 5791 "parser.tab.c"
    break;

  case 278: /* fof_unit_formula: fof_unary_formula  */
#line 1130 "parser.y"
                      { (yyval.data) = Tptp_mk_FofUnitFormula_fofUnaryFormula((yyvsp[0].data)); }
#line 5797 "parser.tab.c"
    break;

  case 279: /* fof_unitary_formula: fof_quantified_formula  */
#line 1134 "parser.y"
                         { (yyval.data) = Tptp_mk_FofUnitaryFormula_fofQuantifiedFormula((yyvsp[0].data)); }
#line 5803 "parser.tab.c"
    break;

  case 280: /* fof_unitary_formula: fof_atomic_formula  */
#line 1135 "parser.y"
                       { (yyval.data) = Tptp_mk_FofUnitaryFormula_fofAtomicFormula((yyvsp[0].data)); }
#line 5809 "parser.tab.c"
    break;

  case 281: /* fof_unitary_formula: "(" fof_logic_formula ")"  */
#line 1136 "parser.y"
                              { (yyval.data) = Tptp_mk_FofUnitaryFormula_fofLogicFormula((yyvsp[-1].data)); }
#line 5815 "parser.tab.c"
    break;

  case 282: /* fof_quantified_formula: fof_quantifier "[" fof_variable_list "]" ":" fof_unit_formula  */
#line 1140 "parser.y"
                                                                { (yyval.data) = Tptp_mk_FofQuantifiedFormula_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[0].data)); }
#line 5821 "parser.tab.c"
    break;

  case 283: /* fof_variable_list: variable  */
#line 1144 "parser.y"
           { (yyval.data) = Tptp_mk_FofVariableList_variable((yyvsp[0].data)); }
#line 5827 "parser.tab.c"
    break;

  case 284: /* fof_variable_list: variable "," fof_variable_list  */
#line 1145 "parser.y"
                                   { (yyval.data) = Tptp_mk_FofVariableList_variableFofVariableList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5833 "parser.tab.c"
    break;

  case 285: /* fof_atomic_formula: fof_plain_atomic_formula  */
#line 1149 "parser.y"
                           { (yyval.data) = Tptp_mk_FofAtomicFormula_fofPlainAtomicFormula((yyvsp[0].data)); }
#line 5839 "parser.tab.c"
    break;

  case 286: /* fof_atomic_formula: fof_defined_atomic_formula  */
#line 1150 "parser.y"
                               { (yyval.data) = Tptp_mk_FofAtomicFormula_fofDefinedAtomicFormula((yyvsp[0].data)); }
#line 5845 "parser.tab.c"
    break;

  case 287: /* fof_atomic_formula: fof_system_atomic_formula  */
#line 1151 "parser.y"
                              { (yyval.data) = Tptp_mk_FofAtomicFormula_fofSystemAtomicFormula((yyvsp[0].data)); }
#line 5851 "parser.tab.c"
    break;

  case 288: /* fof_plain_atomic_formula: fof_plain_term  */
#line 1155 "parser.y"
                 { (yyval.data) = Tptp_mk_FofPlainAtomicFormula_mk((yyvsp[0].data)); }
#line 5857 "parser.tab.c"
    break;

  case 289: /* fof_defined_atomic_formula: fof_defined_plain_formula  */
#line 1159 "parser.y"
                            { (yyval.data) = Tptp_mk_FofDefinedAtomicFormula_fofDefinedPlainFormula((yyvsp[0].data)); }
#line 5863 "parser.tab.c"
    break;

  case 290: /* fof_defined_atomic_formula: fof_defined_infix_formula  */
#line 1160 "parser.y"
                              { (yyval.data) = Tptp_mk_FofDefinedAtomicFormula_fofDefinedInfixFormula((yyvsp[0].data)); }
#line 5869 "parser.tab.c"
    break;

  case 291: /* fof_defined_plain_formula: fof_defined_plain_term  */
#line 1164 "parser.y"
                         { (yyval.data) = Tptp_mk_FofDefinedPlainFormula_mk((yyvsp[0].data)); }
#line 5875 "parser.tab.c"
    break;

  case 292: /* fof_defined_infix_formula: fof_term defined_infix_pred fof_term  */
#line 1168 "parser.y"
                                       { (yyval.data) = Tptp_mk_FofDefinedInfixFormula_mk((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5881 "parser.tab.c"
    break;

  case 293: /* fof_system_atomic_formula: fof_system_term  */
#line 1172 "parser.y"
                  { (yyval.data) = Tptp_mk_FofSystemAtomicFormula_mk((yyvsp[0].data)); }
#line 5887 "parser.tab.c"
    break;

  case 294: /* fof_plain_term: constant  */
#line 1176 "parser.y"
           { (yyval.data) = Tptp_mk_FofPlainTerm_constant((yyvsp[0].data)); }
#line 5893 "parser.tab.c"
    break;

  case 295: /* fof_plain_term: functor "(" fof_arguments ")"  */
#line 1177 "parser.y"
                                  { (yyval.data) = Tptp_mk_FofPlainTerm_functorFofArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5899 "parser.tab.c"
    break;

  case 296: /* fof_defined_term: defined_term  */
#line 1181 "parser.y"
               { (yyval.data) = Tptp_mk_FofDefinedTerm_definedTerm((yyvsp[0].data)); }
#line 5905 "parser.tab.c"
    break;

  case 297: /* fof_defined_term: fof_defined_atomic_term  */
#line 1182 "parser.y"
                            { (yyval.data) = Tptp_mk_FofDefinedTerm_fofDefinedAtomicTerm((yyvsp[0].data)); }
#line 5911 "parser.tab.c"
    break;

  case 298: /* fof_defined_atomic_term: fof_defined_plain_term  */
#line 1186 "parser.y"
                         { (yyval.data) = Tptp_mk_FofDefinedAtomicTerm_mk((yyvsp[0].data)); }
#line 5917 "parser.tab.c"
    break;

  case 299: /* fof_defined_plain_term: defined_constant  */
#line 1190 "parser.y"
                   { (yyval.data) = Tptp_mk_FofDefinedPlainTerm_definedConstant((yyvsp[0].data)); }
#line 5923 "parser.tab.c"
    break;

  case 300: /* fof_defined_plain_term: defined_functor "(" fof_arguments ")"  */
#line 1191 "parser.y"
                                          { (yyval.data) = Tptp_mk_FofDefinedPlainTerm_definedFunctorFofArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5929 "parser.tab.c"
    break;

  case 301: /* fof_system_term: system_constant  */
#line 1195 "parser.y"
                  { (yyval.data) = Tptp_mk_FofSystemTerm_systemConstant((yyvsp[0].data)); }
#line 5935 "parser.tab.c"
    break;

  case 302: /* fof_system_term: system_functor "(" fof_arguments ")"  */
#line 1196 "parser.y"
                                         { (yyval.data) = Tptp_mk_FofSystemTerm_systemFunctorFofArguments((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 5941 "parser.tab.c"
    break;

  case 303: /* fof_arguments: fof_term  */
#line 1200 "parser.y"
           { (yyval.data) = Tptp_mk_FofArguments_fofTerm((yyvsp[0].data)); }
#line 5947 "parser.tab.c"
    break;

  case 304: /* fof_arguments: fof_term "," fof_arguments  */
#line 1201 "parser.y"
                               { (yyval.data) = Tptp_mk_FofArguments_fofTermFofArguments((yyvsp[-2].data), (yyvsp[0].data)); }
#line 5953 "parser.tab.c"
    break;

  case 305: /* fof_term: fof_function_term  */
#line 1205 "parser.y"
                    { (yyval.data) = Tptp_mk_FofTerm_fofFunctionTerm((yyvsp[0].data)); }
#line 5959 "parser.tab.c"
    break;

  case 306: /* fof_term: variable  */
#line 1206 "parser.y"
             { (yyval.data) = Tptp_mk_FofTerm_variable((yyvsp[0].data)); }
#line 5965 "parser.tab.c"
    break;

  case 307: /* fof_function_term: fof_plain_term  */
#line 1210 "parser.y"
                 { (yyval.data) = Tptp_mk_FofFunctionTerm_fofPlainTerm((yyvsp[0].data)); }
#line 5971 "parser.tab.c"
    break;

  case 308: /* fof_function_term: fof_defined_term  */
#line 1211 "parser.y"
                     { (yyval.data) = Tptp_mk_FofFunctionTerm_fofDefinedTerm((yyvsp[0].data)); }
#line 5977 "parser.tab.c"
    break;

  case 309: /* fof_function_term: fof_system_term  */
#line 1212 "parser.y"
                    { (yyval.data) = Tptp_mk_FofFunctionTerm_fofSystemTerm((yyvsp[0].data)); }
#line 5983 "parser.tab.c"
    break;

  case 310: /* fof_sequent: fof_formula_tuple gentzen_arrow fof_formula_tuple  */
#line 1216 "parser.y"
                                                    { (yyval.data) = Tptp_mk_FofSequent_fofFormulaTupleGentzenArrowFofFormulaTuple((yyvsp[-2].data), (yyvsp[-1].data), (yyvsp[0].data)); }
#line 5989 "parser.tab.c"
    break;

  case 311: /* fof_sequent: "(" fof_sequent ")"  */
#line 1217 "parser.y"
                        { (yyval.data) = Tptp_mk_FofSequent_fofSequent((yyvsp[-1].data)); }
#line 5995 "parser.tab.c"
    break;

  case 312: /* fof_formula_tuple: "[]"  */
#line 1221 "parser.y"
       { (yyval.data) = Tptp_mk_FofFormulaTuple_empty; }
#line 6001 "parser.tab.c"
    break;

  case 313: /* fof_formula_tuple: "[" fof_formula_tuple_list "]"  */
#line 1222 "parser.y"
                                   { (yyval.data) = Tptp_mk_FofFormulaTuple_fofFormulaTupleList((yyvsp[-1].data)); }
#line 6007 "parser.tab.c"
    break;

  case 314: /* fof_formula_tuple_list: fof_logic_formula comma_fof_logic_formula_list  */
#line 1226 "parser.y"
                                                 { (yyval.data) = Tptp_mk_FofFormulaTupleList_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 6013 "parser.tab.c"
    break;

  case 315: /* comma_fof_logic_formula_list: %empty  */
#line 1230 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 6019 "parser.tab.c"
    break;

  case 316: /* comma_fof_logic_formula_list: comma_fof_logic_formula_list comma_fof_logic_formula  */
#line 1231 "parser.y"
                                                         { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 6025 "parser.tab.c"
    break;

  case 317: /* comma_fof_logic_formula: "," fof_logic_formula  */
#line 1235 "parser.y"
                        { (yyval.data) = Tptp_mk_CommaFofLogicFormula_mk((yyvsp[0].data)); }
#line 6031 "parser.tab.c"
    break;

  case 318: /* cnf_formula: cnf_disjunction  */
#line 1239 "parser.y"
                  { (yyval.data) = Tptp_mk_CnfFormula_cnfDisjunction((yyvsp[0].data)); }
#line 6037 "parser.tab.c"
    break;

  case 319: /* cnf_formula: "(" cnf_formula ")"  */
#line 1240 "parser.y"
                        { (yyval.data) = Tptp_mk_CnfFormula_cnfFormula((yyvsp[-1].data)); }
#line 6043 "parser.tab.c"
    break;

  case 320: /* cnf_disjunction: cnf_literal  */
#line 1244 "parser.y"
              { (yyval.data) = Tptp_mk_CnfDisjunction_cnfLiteral((yyvsp[0].data)); }
#line 6049 "parser.tab.c"
    break;

  case 321: /* cnf_disjunction: cnf_disjunction "|" cnf_literal  */
#line 1245 "parser.y"
                                      { (yyval.data) = Tptp_mk_CnfDisjunction_cnfDisjunctionCnfLiteral((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6055 "parser.tab.c"
    break;

  case 322: /* cnf_literal: fof_atomic_formula  */
#line 1249 "parser.y"
                     { (yyval.data) = Tptp_mk_CnfLiteral_fofAtomicFormula((yyvsp[0].data)); }
#line 6061 "parser.tab.c"
    break;

  case 323: /* cnf_literal: "~" fof_atomic_formula  */
#line 1250 "parser.y"
                           { (yyval.data) = Tptp_mk_CnfLiteral_fofAtomicFormulaNegated((yyvsp[0].data)); }
#line 6067 "parser.tab.c"
    break;

  case 324: /* cnf_literal: "~" "(" fof_atomic_formula ")"  */
#line 1251 "parser.y"
                                   { (yyval.data) = Tptp_mk_CnfLiteral_fofAtomicFormulaNegated((yyvsp[-1].data)); }
#line 6073 "parser.tab.c"
    break;

  case 325: /* cnf_literal: fof_infix_unary  */
#line 1252 "parser.y"
                    { (yyval.data) = Tptp_mk_CnfLiteral_fofInfixUnary((yyvsp[0].data)); }
#line 6079 "parser.tab.c"
    break;

  case 326: /* thf_quantifier: tff_quantifier  */
#line 1256 "parser.y"
                 { (yyval.data) = Tptp_mk_ThfQuantifier_tffQuantifier((yyvsp[0].data)); }
#line 6085 "parser.tab.c"
    break;

  case 327: /* thf_quantifier: th0_quantifier  */
#line 1257 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfQuantifier_th0Quantifier((yyvsp[0].data)); }
#line 6091 "parser.tab.c"
    break;

  case 328: /* thf_quantifier: type_quantifier  */
#line 1258 "parser.y"
                    { (yyval.data) = Tptp_mk_ThfQuantifier_typeQuantifier((yyvsp[0].data)); }
#line 6097 "parser.tab.c"
    break;

  case 329: /* thf_unary_connective: unary_connective  */
#line 1262 "parser.y"
                   { (yyval.data) = Tptp_mk_ThfUnaryConnective_unaryConnective((yyvsp[0].data)); }
#line 6103 "parser.tab.c"
    break;

  case 330: /* thf_unary_connective: ntf_short_connective  */
#line 1263 "parser.y"
                         { (yyval.data) = Tptp_mk_ThfUnaryConnective_ntfShortConnective((yyvsp[0].data)); }
#line 6109 "parser.tab.c"
    break;

  case 331: /* th0_quantifier: "^"  */
#line 1267 "parser.y"
      { (yyval.data) = Tptp_mk_Th0Quantifier_caret; }
#line 6115 "parser.tab.c"
    break;

  case 332: /* th0_quantifier: "@+"  */
#line 1268 "parser.y"
         { (yyval.data) = Tptp_mk_Th0Quantifier_atPlus; }
#line 6121 "parser.tab.c"
    break;

  case 333: /* th0_quantifier: "@-"  */
#line 1269 "parser.y"
         { (yyval.data) = Tptp_mk_Th0Quantifier_atMinus; }
#line 6127 "parser.tab.c"
    break;

  case 334: /* type_quantifier: "!>"  */
#line 1273 "parser.y"
       { (yyval.data) = Tptp_mk_TypeQuantifier_exclamationArrow; }
#line 6133 "parser.tab.c"
    break;

  case 335: /* type_quantifier: "?*"  */
#line 1274 "parser.y"
         { (yyval.data) = Tptp_mk_TypeQuantifier_questionStar; }
#line 6139 "parser.tab.c"
    break;

  case 336: /* subtype_sign: "<<"  */
#line 1278 "parser.y"
       { (yyval.data) = Tptp_mk_SubtypeSign_mk; }
#line 6145 "parser.tab.c"
    break;

  case 337: /* tff_unary_connective: unary_connective  */
#line 1282 "parser.y"
                   { (yyval.data) = Tptp_mk_TffUnaryConnective_unaryConnective((yyvsp[0].data)); }
#line 6151 "parser.tab.c"
    break;

  case 338: /* tff_unary_connective: ntf_short_connective  */
#line 1283 "parser.y"
                         { (yyval.data) = Tptp_mk_TffUnaryConnective_ntfShortConnective((yyvsp[0].data)); }
#line 6157 "parser.tab.c"
    break;

  case 339: /* tff_quantifier: fof_quantifier  */
#line 1287 "parser.y"
                 { (yyval.data) = Tptp_mk_TffQuantifier_fofQuantifier((yyvsp[0].data)); }
#line 6163 "parser.tab.c"
    break;

  case 340: /* tff_quantifier: "#"  */
#line 1288 "parser.y"
         { (yyval.data) = Tptp_mk_TffQuantifier_hash; }
#line 6169 "parser.tab.c"
    break;

  case 341: /* fof_quantifier: "!"  */
#line 1292 "parser.y"
      { (yyval.data) = Tptp_mk_FofQuantifier_exclamation; }
#line 6175 "parser.tab.c"
    break;

  case 342: /* fof_quantifier: "?"  */
#line 1293 "parser.y"
        { (yyval.data) = Tptp_mk_FofQuantifier_question; }
#line 6181 "parser.tab.c"
    break;

  case 343: /* nonassoc_connective: "<=>"  */
#line 1297 "parser.y"
        { (yyval.data) = Tptp_mk_NonassocConnective_iff; }
#line 6187 "parser.tab.c"
    break;

  case 344: /* nonassoc_connective: "=>"  */
#line 1298 "parser.y"
         { (yyval.data) = Tptp_mk_NonassocConnective_fi; }
#line 6193 "parser.tab.c"
    break;

  case 345: /* nonassoc_connective: "<="  */
#line 1299 "parser.y"
         { (yyval.data) = Tptp_mk_NonassocConnective_if; }
#line 6199 "parser.tab.c"
    break;

  case 346: /* nonassoc_connective: "<~>"  */
#line 1300 "parser.y"
          { (yyval.data) = Tptp_mk_NonassocConnective_xor; }
#line 6205 "parser.tab.c"
    break;

  case 347: /* nonassoc_connective: "~" "|"  */
#line 1301 "parser.y"
              { (yyval.data) = Tptp_mk_NonassocConnective_nor; }
#line 6211 "parser.tab.c"
    break;

  case 348: /* nonassoc_connective: "~&"  */
#line 1302 "parser.y"
         { (yyval.data) = Tptp_mk_NonassocConnective_nand; }
#line 6217 "parser.tab.c"
    break;

  case 349: /* assoc_connective: "|"  */
#line 1306 "parser.y"
        { (yyval.data) = Tptp_mk_AssocConnective_or; }
#line 6223 "parser.tab.c"
    break;

  case 350: /* assoc_connective: "&"  */
#line 1307 "parser.y"
        { (yyval.data) = Tptp_mk_AssocConnective_and; }
#line 6229 "parser.tab.c"
    break;

  case 351: /* unary_connective: "~"  */
#line 1311 "parser.y"
      { (yyval.data) = Tptp_mk_UnaryConnective_mk; }
#line 6235 "parser.tab.c"
    break;

  case 352: /* gentzen_arrow: "-->"  */
#line 1315 "parser.y"
        { (yyval.data) = Tptp_mk_GentzenArrow_mk; }
#line 6241 "parser.tab.c"
    break;

  case 353: /* assignment: ":="  */
#line 1319 "parser.y"
       { (yyval.data) = Tptp_mk_Assignment_mk; }
#line 6247 "parser.tab.c"
    break;

  case 354: /* identical: "=="  */
#line 1323 "parser.y"
       { (yyval.data) = Tptp_mk_Identical_mk; }
#line 6253 "parser.tab.c"
    break;

  case 355: /* type_constant: type_functor  */
#line 1327 "parser.y"
               { (yyval.data) = Tptp_mk_TypeConstant_mk((yyvsp[0].data)); }
#line 6259 "parser.tab.c"
    break;

  case 356: /* type_functor: atomic_word  */
#line 1331 "parser.y"
              { (yyval.data) = Tptp_mk_TypeFunctor_mk((yyvsp[0].data)); }
#line 6265 "parser.tab.c"
    break;

  case 357: /* defined_type: atomic_defined_word  */
#line 1335 "parser.y"
                      { (yyval.data) = Tptp_mk_DefinedType_mk((yyvsp[0].data)); }
#line 6271 "parser.tab.c"
    break;

  case 358: /* atom: untyped_atom  */
#line 1339 "parser.y"
               { (yyval.data) = Tptp_mk_Atom_untypedAtom((yyvsp[0].data)); }
#line 6277 "parser.tab.c"
    break;

  case 359: /* atom: defined_constant  */
#line 1340 "parser.y"
                     { (yyval.data) = Tptp_mk_Atom_definedConstant((yyvsp[0].data)); }
#line 6283 "parser.tab.c"
    break;

  case 360: /* untyped_atom: constant  */
#line 1344 "parser.y"
           { (yyval.data) = Tptp_mk_UntypedAtom_constant((yyvsp[0].data)); }
#line 6289 "parser.tab.c"
    break;

  case 361: /* untyped_atom: system_constant  */
#line 1345 "parser.y"
                    { (yyval.data) = Tptp_mk_UntypedAtom_systemConstant((yyvsp[0].data)); }
#line 6295 "parser.tab.c"
    break;

  case 362: /* defined_infix_pred: infix_equality  */
#line 1349 "parser.y"
                 { (yyval.data) = Tptp_mk_DefinedInfixPred_mk((yyvsp[0].data)); }
#line 6301 "parser.tab.c"
    break;

  case 363: /* infix_equality: "="  */
#line 1353 "parser.y"
      { (yyval.data) = Tptp_mk_InfixEquality_mk; }
#line 6307 "parser.tab.c"
    break;

  case 364: /* infix_inequality: "!="  */
#line 1357 "parser.y"
       { (yyval.data) = Tptp_mk_InfixInequality_mk; }
#line 6313 "parser.tab.c"
    break;

  case 365: /* constant: functor  */
#line 1361 "parser.y"
          { (yyval.data) = Tptp_mk_Constant_mk((yyvsp[0].data)); }
#line 6319 "parser.tab.c"
    break;

  case 366: /* functor: atomic_word  */
#line 1365 "parser.y"
              { (yyval.data) = Tptp_mk_Functor_mk((yyvsp[0].data)); }
#line 6325 "parser.tab.c"
    break;

  case 367: /* defined_constant: defined_functor  */
#line 1369 "parser.y"
                  { (yyval.data) = Tptp_mk_DefinedConstant_mk((yyvsp[0].data)); }
#line 6331 "parser.tab.c"
    break;

  case 368: /* defined_functor: atomic_defined_word  */
#line 1373 "parser.y"
                      { (yyval.data) = Tptp_mk_DefinedFunctor_mk((yyvsp[0].data)); }
#line 6337 "parser.tab.c"
    break;

  case 369: /* system_constant: system_functor  */
#line 1377 "parser.y"
                 { (yyval.data) = Tptp_mk_SystemConstant_mk((yyvsp[0].data)); }
#line 6343 "parser.tab.c"
    break;

  case 370: /* system_functor: atomic_system_word  */
#line 1381 "parser.y"
                     { (yyval.data) = Tptp_mk_SystemFunctor_mk((yyvsp[0].data)); }
#line 6349 "parser.tab.c"
    break;

  case 371: /* def_or_sys_constant: defined_constant  */
#line 1385 "parser.y"
                   { (yyval.data) = Tptp_mk_DefOrSysConstant_definedConstant((yyvsp[0].data)); }
#line 6355 "parser.tab.c"
    break;

  case 372: /* def_or_sys_constant: system_constant  */
#line 1386 "parser.y"
                    { (yyval.data) = Tptp_mk_DefOrSysConstant_systemConstant((yyvsp[0].data)); }
#line 6361 "parser.tab.c"
    break;

  case 373: /* th1_defined_term: "!!"  */
#line 1390 "parser.y"
       { (yyval.data) = Tptp_mk_Th1DefinedTerm_doubleExclamation; }
#line 6367 "parser.tab.c"
    break;

  case 374: /* th1_defined_term: "??"  */
#line 1391 "parser.y"
         { (yyval.data) = Tptp_mk_Th1DefinedTerm_doubleQuestion; }
#line 6373 "parser.tab.c"
    break;

  case 375: /* th1_defined_term: "@@+"  */
#line 1392 "parser.y"
          { (yyval.data) = Tptp_mk_Th1DefinedTerm_doubleAtPlus; }
#line 6379 "parser.tab.c"
    break;

  case 376: /* th1_defined_term: "@@-"  */
#line 1393 "parser.y"
          { (yyval.data) = Tptp_mk_Th1DefinedTerm_doubleAtMinus; }
#line 6385 "parser.tab.c"
    break;

  case 377: /* th1_defined_term: "@="  */
#line 1394 "parser.y"
         { (yyval.data) = Tptp_mk_Th1DefinedTerm_atEquals; }
#line 6391 "parser.tab.c"
    break;

  case 378: /* distinct_object: DISTINCT_OBJECT  */
#line 1398 "parser.y"
                  { (yyval.data) = Tptp_mk_DistinctObject_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6397 "parser.tab.c"
    break;

  case 379: /* defined_term: number  */
#line 1402 "parser.y"
         { (yyval.data) = Tptp_mk_DefinedTerm_number((yyvsp[0].data)); }
#line 6403 "parser.tab.c"
    break;

  case 380: /* defined_term: distinct_object  */
#line 1403 "parser.y"
                    { (yyval.data) = Tptp_mk_DefinedTerm_distinctObject((yyvsp[0].data)); }
#line 6409 "parser.tab.c"
    break;

  case 381: /* upper_word: UPPER_WORD  */
#line 1407 "parser.y"
             { (yyval.data) = Tptp_mk_UpperWord_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6415 "parser.tab.c"
    break;

  case 382: /* variable: upper_word  */
#line 1411 "parser.y"
             { (yyval.data) = Tptp_mk_Variable_mk((yyvsp[0].data)); }
#line 6421 "parser.tab.c"
    break;

  case 383: /* source: "unknown"  */
#line 1416 "parser.y"
            { (yyval.data) = Tptp_mk_Source_unknown; }
#line 6427 "parser.tab.c"
    break;

  case 384: /* source: dag_source  */
#line 1417 "parser.y"
               { (yyval.data) = Tptp_mk_Source_dagSource((yyvsp[0].data)); }
#line 6433 "parser.tab.c"
    break;

  case 385: /* source: internal_source  */
#line 1418 "parser.y"
                    { (yyval.data) = Tptp_mk_Source_internalSource((yyvsp[0].data)); }
#line 6439 "parser.tab.c"
    break;

  case 386: /* source: external_source  */
#line 1419 "parser.y"
                    { (yyval.data) = Tptp_mk_Source_externalSource((yyvsp[0].data)); }
#line 6445 "parser.tab.c"
    break;

  case 387: /* source: "[" sources "]"  */
#line 1420 "parser.y"
                    { (yyval.data) = Tptp_mk_Source_sources((yyvsp[-1].data)); }
#line 6451 "parser.tab.c"
    break;

  case 388: /* sources: source  */
#line 1424 "parser.y"
         { (yyval.data) = Tptp_mk_Sources_source((yyvsp[0].data)); }
#line 6457 "parser.tab.c"
    break;

  case 389: /* sources: source "," sources  */
#line 1425 "parser.y"
                       { (yyval.data) = Tptp_mk_Sources_sourceSources((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6463 "parser.tab.c"
    break;

  case 390: /* dag_source: name  */
#line 1429 "parser.y"
       { (yyval.data) = Tptp_mk_DagSource_name((yyvsp[0].data)); }
#line 6469 "parser.tab.c"
    break;

  case 391: /* dag_source: inference_record  */
#line 1430 "parser.y"
                     { (yyval.data) = Tptp_mk_DagSource_inferenceRecord((yyvsp[0].data)); }
#line 6475 "parser.tab.c"
    break;

  case 392: /* inference_record: "inference(" inference_rule "," useful_info "," parents ")"  */
#line 1434 "parser.y"
                                                              { (yyval.data) = Tptp_mk_InferenceRecord_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6481 "parser.tab.c"
    break;

  case 393: /* inference_rule: atomic_word  */
#line 1438 "parser.y"
              { (yyval.data) = Tptp_mk_InferenceRule_mk((yyvsp[0].data)); }
#line 6487 "parser.tab.c"
    break;

  case 394: /* internal_source: "introduced(" intro_type "," useful_info "," parents ")"  */
#line 1442 "parser.y"
                                                           { (yyval.data) = Tptp_mk_InternalSource_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6493 "parser.tab.c"
    break;

  case 395: /* intro_type: atomic_word  */
#line 1446 "parser.y"
              { (yyval.data) = Tptp_mk_IntroType_mk((yyvsp[0].data)); }
#line 6499 "parser.tab.c"
    break;

  case 396: /* external_source: file_source  */
#line 1450 "parser.y"
              { (yyval.data) = Tptp_mk_ExternalSource_fileSource((yyvsp[0].data)); }
#line 6505 "parser.tab.c"
    break;

  case 397: /* external_source: theory  */
#line 1451 "parser.y"
           { (yyval.data) = Tptp_mk_ExternalSource_theory((yyvsp[0].data)); }
#line 6511 "parser.tab.c"
    break;

  case 398: /* external_source: creator_source  */
#line 1452 "parser.y"
                   { (yyval.data) = Tptp_mk_ExternalSource_creatorSource((yyvsp[0].data)); }
#line 6517 "parser.tab.c"
    break;

  case 399: /* file_source: "file(" file_name file_info ")"  */
#line 1456 "parser.y"
                                  { (yyval.data) = Tptp_mk_FileSource_mk((yyvsp[-2].data), (yyvsp[-1].data)); }
#line 6523 "parser.tab.c"
    break;

  case 400: /* file_info: "," name  */
#line 1460 "parser.y"
           { (yyval.data) = Tptp_mk_FileInfo_name((yyvsp[0].data)); }
#line 6529 "parser.tab.c"
    break;

  case 401: /* file_info: %empty  */
#line 1461 "parser.y"
           { (yyval.data) = Tptp_mk_FileInfo_nothing; }
#line 6535 "parser.tab.c"
    break;

  case 402: /* theory: "theory(" theory_name optional_info ")"  */
#line 1465 "parser.y"
                                          { (yyval.data) = Tptp_mk_Theory_mk((yyvsp[-2].data), (yyvsp[-1].data)); }
#line 6541 "parser.tab.c"
    break;

  case 403: /* theory_name: atomic_word  */
#line 1469 "parser.y"
              { (yyval.data) = Tptp_mk_TheoryName_mk((yyvsp[0].data)); }
#line 6547 "parser.tab.c"
    break;

  case 404: /* creator_source: "creator(" creator_name "," useful_info "," parents ")"  */
#line 1473 "parser.y"
                                                          { (yyval.data) = Tptp_mk_CreatorSource_mk((yyvsp[-5].data), (yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6553 "parser.tab.c"
    break;

  case 405: /* creator_name: atomic_word  */
#line 1477 "parser.y"
              { (yyval.data) = Tptp_mk_CreatorName_mk((yyvsp[0].data)); }
#line 6559 "parser.tab.c"
    break;

  case 406: /* parents: "[]"  */
#line 1481 "parser.y"
       { (yyval.data) = Tptp_mk_Parents_empty; }
#line 6565 "parser.tab.c"
    break;

  case 407: /* parents: "[" parent_list "]"  */
#line 1482 "parser.y"
                        { (yyval.data) = Tptp_mk_Parents_parentList((yyvsp[-1].data)); }
#line 6571 "parser.tab.c"
    break;

  case 408: /* parent_list: parent_info comma_parent_info_list  */
#line 1486 "parser.y"
                                     { (yyval.data) = Tptp_mk_ParentList_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 6577 "parser.tab.c"
    break;

  case 409: /* comma_parent_info_list: %empty  */
#line 1490 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 6583 "parser.tab.c"
    break;

  case 410: /* comma_parent_info_list: comma_parent_info_list comma_parent_info  */
#line 1491 "parser.y"
                                             { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 6589 "parser.tab.c"
    break;

  case 411: /* comma_parent_info: "," parent_info  */
#line 1495 "parser.y"
                  { (yyval.data) = Tptp_mk_CommaParentInfo_mk((yyvsp[0].data)); }
#line 6595 "parser.tab.c"
    break;

  case 412: /* parent_info: source parent_details  */
#line 1499 "parser.y"
                        { (yyval.data) = Tptp_mk_ParentInfo_mk((yyvsp[-1].data), (yyvsp[0].data)); }
#line 6601 "parser.tab.c"
    break;

  case 413: /* parent_details: ":" general_term  */
#line 1503 "parser.y"
                   { (yyval.data) = Tptp_mk_ParentDetails_generalTerm((yyvsp[0].data)); }
#line 6607 "parser.tab.c"
    break;

  case 414: /* parent_details: %empty  */
#line 1504 "parser.y"
           { (yyval.data) = Tptp_mk_ParentDetails_nothing; }
#line 6613 "parser.tab.c"
    break;

  case 415: /* optional_info: "," useful_info  */
#line 1508 "parser.y"
                  { (yyval.data) = Tptp_mk_OptionalInfo_usefulInfo((yyvsp[0].data)); }
#line 6619 "parser.tab.c"
    break;

  case 416: /* optional_info: %empty  */
#line 1509 "parser.y"
           { (yyval.data) = Tptp_mk_OptionalInfo_nothing; }
#line 6625 "parser.tab.c"
    break;

  case 417: /* useful_info: general_list  */
#line 1513 "parser.y"
               { (yyval.data) = Tptp_mk_UsefulInfo_mk((yyvsp[0].data)); }
#line 6631 "parser.tab.c"
    break;

  case 418: /* include: "include(" file_name include_optionals ")."  */
#line 1517 "parser.y"
                                              { (yyval.data) = Tptp_mk_Include_mk((yyvsp[-2].data), (yyvsp[-1].data)); }
#line 6637 "parser.tab.c"
    break;

  case 419: /* include_optionals: %empty  */
#line 1521 "parser.y"
         {(yyval.data) = Tptp_mk_IncludeOptionals_nothing; }
#line 6643 "parser.tab.c"
    break;

  case 420: /* include_optionals: "," formula_selection  */
#line 1522 "parser.y"
                          { (yyval.data) = Tptp_mk_IncludeOptionals_formulaSelection((yyvsp[0].data)); }
#line 6649 "parser.tab.c"
    break;

  case 421: /* include_optionals: "," formula_selection "," space_name  */
#line 1523 "parser.y"
                                         { (yyval.data) = Tptp_mk_IncludeOptionals_formulaSelectionSpaceName((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6655 "parser.tab.c"
    break;

  case 422: /* formula_selection: "[" name_list "]"  */
#line 1527 "parser.y"
                    { (yyval.data) = Tptp_mk_FormulaSelection_nameList((yyvsp[-1].data)); }
#line 6661 "parser.tab.c"
    break;

  case 423: /* formula_selection: "*"  */
#line 1528 "parser.y"
         { (yyval.data) = Tptp_mk_FormulaSelection_star; }
#line 6667 "parser.tab.c"
    break;

  case 424: /* name_list: name  */
#line 1532 "parser.y"
       { (yyval.data) = Tptp_mk_NameList_name((yyvsp[0].data)); }
#line 6673 "parser.tab.c"
    break;

  case 425: /* name_list: name "," name_list  */
#line 1533 "parser.y"
                       { (yyval.data) = Tptp_mk_NameList_nameNameList((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6679 "parser.tab.c"
    break;

  case 426: /* space_name: name  */
#line 1537 "parser.y"
       { (yyval.data) = Tptp_mk_SpaceName_mk((yyvsp[0].data)); }
#line 6685 "parser.tab.c"
    break;

  case 427: /* general_term: general_data  */
#line 1541 "parser.y"
               { (yyval.data) = Tptp_mk_GeneralTerm_generalData((yyvsp[0].data)); }
#line 6691 "parser.tab.c"
    break;

  case 428: /* general_term: general_data ":" general_term  */
#line 1542 "parser.y"
                                  { (yyval.data) = Tptp_mk_GeneralTerm_generalDataGeneralTerm((yyvsp[-2].data), (yyvsp[0].data)); }
#line 6697 "parser.tab.c"
    break;

  case 429: /* general_term: general_list  */
#line 1543 "parser.y"
                 { (yyval.data) = Tptp_mk_GeneralTerm_generalList((yyvsp[0].data)); }
#line 6703 "parser.tab.c"
    break;

  case 430: /* general_data: atomic_word  */
#line 1547 "parser.y"
              { (yyval.data) = Tptp_mk_GeneralData_atomicWord((yyvsp[0].data)); }
#line 6709 "parser.tab.c"
    break;

  case 431: /* general_data: general_function  */
#line 1548 "parser.y"
                     { (yyval.data) = Tptp_mk_GeneralData_generalFunction((yyvsp[0].data)); }
#line 6715 "parser.tab.c"
    break;

  case 432: /* general_data: variable  */
#line 1549 "parser.y"
             { (yyval.data) = Tptp_mk_GeneralData_variable((yyvsp[0].data)); }
#line 6721 "parser.tab.c"
    break;

  case 433: /* general_data: number  */
#line 1550 "parser.y"
           { (yyval.data) = Tptp_mk_GeneralData_number((yyvsp[0].data)); }
#line 6727 "parser.tab.c"
    break;

  case 434: /* general_data: distinct_object  */
#line 1551 "parser.y"
                    { (yyval.data) = Tptp_mk_GeneralData_distinctObject((yyvsp[0].data)); }
#line 6733 "parser.tab.c"
    break;

  case 435: /* general_data: formula_data  */
#line 1552 "parser.y"
                 { (yyval.data) = Tptp_mk_GeneralData_formulaData((yyvsp[0].data)); }
#line 6739 "parser.tab.c"
    break;

  case 436: /* general_function: atomic_word "(" general_terms ")"  */
#line 1556 "parser.y"
                                    { (yyval.data) = Tptp_mk_GeneralFunction_mk((yyvsp[-3].data), (yyvsp[-1].data)); }
#line 6745 "parser.tab.c"
    break;

  case 437: /* formula_data: "$thf(" thf_formula ")"  */
#line 1560 "parser.y"
                          { (yyval.data) = Tptp_mk_FormulaData_thfFormula((yyvsp[-1].data)); }
#line 6751 "parser.tab.c"
    break;

  case 438: /* formula_data: "$tff(" tff_formula ")"  */
#line 1561 "parser.y"
                            { (yyval.data) = Tptp_mk_FormulaData_tffFormula((yyvsp[-1].data)); }
#line 6757 "parser.tab.c"
    break;

  case 439: /* formula_data: "$fof(" fof_formula ")"  */
#line 1562 "parser.y"
                            { (yyval.data) = Tptp_mk_FormulaData_fofFormula((yyvsp[-1].data)); }
#line 6763 "parser.tab.c"
    break;

  case 440: /* formula_data: "$cnf(" cnf_formula ")"  */
#line 1563 "parser.y"
                            { (yyval.data) = Tptp_mk_FormulaData_cnfFormula((yyvsp[-1].data)); }
#line 6769 "parser.tab.c"
    break;

  case 441: /* formula_data: "$fot(" fof_term ")"  */
#line 1564 "parser.y"
                         { (yyval.data) = Tptp_mk_FormulaData_fofTerm((yyvsp[-1].data)); }
#line 6775 "parser.tab.c"
    break;

  case 442: /* general_list: "[]"  */
#line 1568 "parser.y"
       { (yyval.data) = Tptp_mk_GeneralList_empty; }
#line 6781 "parser.tab.c"
    break;

  case 443: /* general_list: "[" general_terms "]"  */
#line 1569 "parser.y"
                          { (yyval.data) = Tptp_mk_GeneralList_generalTerms((yyvsp[-1].data)); }
#line 6787 "parser.tab.c"
    break;

  case 444: /* general_terms: general_term comma_general_term_list  */
#line 1573 "parser.y"
                                       { (yyval.data) = Tptp_mk_GeneralTerms_mk((yyvsp[-1].data), lean_array_to_list((yyvsp[0].data))); }
#line 6793 "parser.tab.c"
    break;

  case 445: /* comma_general_term_list: %empty  */
#line 1577 "parser.y"
         { (yyval.data) = lean_mk_empty_array(); }
#line 6799 "parser.tab.c"
    break;

  case 446: /* comma_general_term_list: comma_general_term_list comma_general_term  */
#line 1578 "parser.y"
                                               { (yyval.data) = lean_array_push((yyvsp[-1].data), (yyvsp[0].data)); }
#line 6805 "parser.tab.c"
    break;

  case 447: /* comma_general_term: "," general_term  */
#line 1582 "parser.y"
                   { (yyval.data) = Tptp_mk_CommaGeneralTerm_mk((yyvsp[0].data)); }
#line 6811 "parser.tab.c"
    break;

  case 448: /* name: atomic_word  */
#line 1586 "parser.y"
              { (yyval.data) = Tptp_mk_Name_atomicWord((yyvsp[0].data)); }
#line 6817 "parser.tab.c"
    break;

  case 449: /* name: integer  */
#line 1587 "parser.y"
            { (yyval.data) = Tptp_mk_Name_integer((yyvsp[0].data)); }
#line 6823 "parser.tab.c"
    break;

  case 450: /* lower_word: "unknown"  */
#line 1591 "parser.y"
          { (yyval.data) = Tptp_mk_LowerWord_mk(lean_mk_string("unknown")); }
#line 6829 "parser.tab.c"
    break;

  case 451: /* lower_word: LOWER_WORD  */
#line 1592 "parser.y"
               { (yyval.data) = Tptp_mk_LowerWord_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6835 "parser.tab.c"
    break;

  case 452: /* single_quoted: SINGLE_QUOTED  */
#line 1596 "parser.y"
                { (yyval.data) = Tptp_mk_SingleQuoted_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6841 "parser.tab.c"
    break;

  case 453: /* back_quoted: BACK_QUOTED  */
#line 1600 "parser.y"
              { (yyval.data) = Tptp_mk_BackQuoted_mk(Tptp_mk_UpperWord_mk(lean_mk_string((yyvsp[0].raw)))); free((yyvsp[0].raw)); }
#line 6847 "parser.tab.c"
    break;

  case 454: /* atomic_word: lower_word  */
#line 1604 "parser.y"
             { (yyval.data) = Tptp_mk_AtomicWord_lowerWord((yyvsp[0].data)); }
#line 6853 "parser.tab.c"
    break;

  case 455: /* atomic_word: single_quoted  */
#line 1605 "parser.y"
                  { (yyval.data) = Tptp_mk_AtomicWord_singleQuoted((yyvsp[0].data)); }
#line 6859 "parser.tab.c"
    break;

  case 456: /* atomic_word: back_quoted  */
#line 1606 "parser.y"
                { (yyval.data) = Tptp_mk_AtomicWord_backQuoted((yyvsp[0].data)); }
#line 6865 "parser.tab.c"
    break;

  case 457: /* dollar_word: DOLLAR_WORD  */
#line 1610 "parser.y"
              { (yyval.data) = Tptp_mk_DollarWord_mk(lean_mk_string((yyvsp[0].raw))) ; free((yyvsp[0].raw)); }
#line 6871 "parser.tab.c"
    break;

  case 458: /* dollar_dollar_word: DOLLAR_DOLLAR_WORD  */
#line 1614 "parser.y"
                     { (yyval.data) = Tptp_mk_DollarDollarWord_mk(lean_mk_string((yyvsp[0].raw))); free((yyvsp[0].raw)); }
#line 6877 "parser.tab.c"
    break;

  case 459: /* atomic_defined_word: dollar_word  */
#line 1618 "parser.y"
              { (yyval.data) = Tptp_mk_AtomicDefinedWord_mk((yyvsp[0].data)); }
#line 6883 "parser.tab.c"
    break;

  case 460: /* atomic_system_word: dollar_dollar_word  */
#line 1622 "parser.y"
                     { (yyval.data) = Tptp_mk_AtomicSystemWord_mk((yyvsp[0].data)); }
#line 6889 "parser.tab.c"
    break;

  case 461: /* integer: INTEGER  */
#line 1626 "parser.y"
          { (yyval.data) = parse_integer((yyvsp[0].raw)); free((yyvsp[0].raw)); }
#line 6895 "parser.tab.c"
    break;

  case 462: /* rational: RATIONAL  */
#line 1630 "parser.y"
           { (yyval.data) = parse_rational((yyvsp[0].raw)); free((yyvsp[0].raw)); }
#line 6901 "parser.tab.c"
    break;

  case 463: /* real: REAL  */
#line 1634 "parser.y"
       { (yyval.data) = parse_real((yyvsp[0].raw)); free((yyvsp[0].raw)); }
#line 6907 "parser.tab.c"
    break;

  case 464: /* number: integer  */
#line 1638 "parser.y"
          { (yyval.data) = Tptp_mk_Number_integer((yyvsp[0].data)); }
#line 6913 "parser.tab.c"
    break;

  case 465: /* number: rational  */
#line 1639 "parser.y"
             { (yyval.data) = Tptp_mk_Number_rational((yyvsp[0].data)); }
#line 6919 "parser.tab.c"
    break;

  case 466: /* number: real  */
#line 1640 "parser.y"
         { (yyval.data) = Tptp_mk_Number_real((yyvsp[0].data)); }
#line 6925 "parser.tab.c"
    break;

  case 467: /* file_name: atomic_word  */
#line 1644 "parser.y"
              { (yyval.data) = Tptp_mk_FileName_mk((yyvsp[0].data)); }
#line 6931 "parser.tab.c"
    break;


#line 6935 "parser.tab.c"

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

#line 1647 "parser.y"


void yyerror(yyscan_t scanner, TptpParseContext *context, const char *message) {
  (void)scanner;
  (void)message;
  context->error = true;
}
