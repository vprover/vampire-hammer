%{
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

%}

/* The generated parser and scanner share only this per-call context. */
%code requires {
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
  } TptpParseContext;
}

%code provides {
  int yylex(YYSTYPE *value, yyscan_t scanner);
  int yylex_init_extra(TptpParseContext *context, yyscan_t *scanner);
  int yylex_destroy(yyscan_t scanner);
  void yyset_in(FILE *input, yyscan_t scanner);
  void yyerror(yyscan_t scanner, TptpParseContext *context, const char *message);
}

%define api.pure full
%parse-param {yyscan_t scanner} {TptpParseContext *context}
%lex-param {yyscan_t scanner}

%define api.token.prefix {TOK_}

%union {
  char *raw;
  lean_object *data;
}

%token <raw> SINGLE_QUOTED
%token <raw> BACK_QUOTED
%token <raw> DISTINCT_OBJECT
%token <raw> DOLLAR_WORD
%token <raw> DOLLAR_DOLLAR_WORD
%token <raw> UPPER_WORD
%token <raw> LOWER_WORD
%token <raw> REAL
%token <raw> RATIONAL
%token <raw> INTEGER

%token EXCLAMATION "!"
%token DOUBLE_EXCLAMATION "!!"
%token EXCLAMATION_EQUALS "!="
%token EXCLAMATION_ARROW "!>"
%token DOLLAR_CNF_PARENOPEN "$cnf("
%token DOLLAR_FOF_PARENOPEN "$fof("
%token DOLLAR_FOT_PARENOPEN "$fot("
%token DOLLAR_LET_PARENOPEN "$let("
%token DOLLAR_TFF_PARENOPEN "$tff("
%token DOLLAR_THF_PARENOPEN "$thf("
%token AMPERSAND "&"
%token PARENOPEN "("
%token PARENOPEN_DOT_PARENCLOSE "(.)"
%token PARENCLOSE ")"
%token PLOSE_DOT ")."
%token PARENCLOSE_BRACECLOSE ")}"
%token COMMA ","
%token HYPEN "-"
%token DOUBLE_HYPHEN_ARROW "-->"
%token DOT "."
%token COLON ":"
%token COLOR_EQUALS ":="
%token DOUBLE_LESS_SIGN "<<"
%token LESS_SIGN_EQUALS "<="
%token LESS_SIGN_EQUALS_ARROW "<=>"
%token LESS_SIGN_TILDE_ARROW "<~>"
%token EQUALS "="
%token DOUBLE_EQUALS "=="
%token EQUALS_ARROW "=>"
%token QUESTION "?"
%token QUESTION_STAR "?*"
%token DOUBLE_QUESTION "??"
%token AT "@"
%token AT_PLUS "@+"
%token AT_MINUS "@-"
%token AT_EQUALS "@="
%token DOUBLE_AT_PLUS "@@+"
%token DOUBLE_AT_MINUS "@@-"
%token BRACKOPEN "["
%token BRACKOPEN_DOT_BRACKCLOSE "[.]"
%token BRACKOPEN_BRACKCLOSE "[]"
%token BRACKCLOSE "]"
%token CARET "^"
%token CNF_PARENOPEN "cnf("
%token CREATOR_PARENOPEN "creator("
%token FILE_PARENOPEN "file("
%token FOF_PARENOPEN "fof("
%token INCLUDE_PARENOPEN "include("
%token INFERENCE_PARENOPEN "inference("
%token INTRODUCED_PARENOPEN "introduced("
%token TCF_PARENOPEN "tcf("
%token TFF_PARENOPEN "tff("
%token THEORY_PARENOPEN "theory("
%token THF_PARENOPEN "thf("
%token TPI_PARENOPEN "tpi("
%token UNKNOWN "unknown"
%token BRACEOPEN "{"
%token BRACEOPEN_DOT_BRACECLOSE "{.}"
%token BRACECLOSE "}"
%token TILDE "~"
%token TILDE_AMPERSAND "~&"
%token VLINE "|"
%token ARROW ">"
%token LESS_SIGN "<"
%token STAR "*"
%token PLUS "+"
%token HASH "#"

%type <data> tptp_file
%type <data> tptp_input_list
%type <data> tptp_input
%type <data> annotated_formula
%type <data> tpi_annotated
%type <data> tpi_formula
%type <data> thf_annotated
%type <data> tff_annotated
%type <data> tcf_annotated
%type <data> fof_annotated
%type <data> cnf_annotated
%type <data> annotations
%type <data> formula_role
%type <data> thf_formula
%type <data> thf_logic_formula
%type <data> thf_binary_formula
%type <data> thf_binary_nonassoc
%type <data> thf_binary_assoc
%type <data> thf_or_formula
%type <data> thf_and_formula
%type <data> thf_apply_formula
%type <data> thf_unit_formula
%type <data> thf_preunit_formula
%type <data> thf_unitary_formula
%type <data> thf_quantified_formula
%type <data> thf_quantification
%type <data> thf_variable_list
%type <data> thf_typed_variable
%type <data> thf_unary_formula
%type <data> thf_prefix_unary
%type <data> thf_infix_unary
%type <data> thf_atomic_formula
%type <data> thf_plain_atomic
%type <data> thf_defined_atomic
%type <data> thf_defined_term
%type <data> thf_defined_infix
%type <data> thf_system_atomic
%type <data> thf_let
%type <data> thf_let_types
%type <data> thf_atom_typing_list
%type <data> thf_let_defns
%type <data> thf_let_defn
%type <data> thf_let_defn_list
%type <data> thf_unitary_term
%type <data> thf_conn_term
%type <data> thf_tuple
%type <data> thf_fof_function
%type <data> thf_arguments
%type <data> thf_formula_list
%type <data> comma_thf_logic_formula_list
%type <data> comma_thf_logic_formula
%type <data> thf_atom_typing
%type <data> thf_top_level_type
%type <data> thf_unitary_type
%type <data> thf_apply_type
%type <data> thf_binary_type
%type <data> thf_mapping_type
%type <data> thf_xprod_type
%type <data> thf_union_type
%type <data> thf_subtype
%type <data> thf_definition
%type <data> thf_sequent
%type <data> tff_formula
%type <data> tff_logic_formula
%type <data> tff_binary_formula
%type <data> tff_binary_nonassoc
%type <data> tff_binary_assoc
%type <data> tff_or_formula
%type <data> tff_and_formula
%type <data> tff_unit_formula
%type <data> tff_preunit_formula
%type <data> tff_unitary_formula
%type <data> txf_unitary_formula
%type <data> tff_quantified_formula
%type <data> tff_variable_list
%type <data> tff_variable
%type <data> tff_typed_variable
%type <data> tff_unary_formula
%type <data> tff_prefix_unary
%type <data> tff_infix_unary
%type <data> tff_atomic_formula
%type <data> tff_plain_atomic
%type <data> tff_defined_atomic
%type <data> tff_defined_plain
%type <data> tff_defined_infix
%type <data> tff_system_atomic
%type <data> txf_let
%type <data> txf_let_types
%type <data> tff_atom_typing_list
%type <data> txf_let_defns
%type <data> txf_let_defn
%type <data> txf_let_LHS
%type <data> txf_let_defn_list
%type <data> nxf_atom
%type <data> tff_term
%type <data> tff_unitary_term
%type <data> txf_tuple
%type <data> tff_arguments
%type <data> comma_tff_term_list
%type <data> comma_tff_term
%type <data> tff_atom_typing
%type <data> tff_top_level_type
%type <data> tff_non_atomic_type
%type <data> tf1_quantified_type
%type <data> tff_monotype
%type <data> tff_unitary_type
%type <data> tff_atomic_type
%type <data> tff_type_arguments
%type <data> tff_mapping_type
%type <data> tff_xprod_type
%type <data> txf_tuple_type
%type <data> tff_type_list
%type <data> tff_subtype
%type <data> txf_definition
%type <data> txf_sequent
%type <data> nhf_long_connective
%type <data> nhf_parameter_list
%type <data> nhf_parameter
%type <data> nhf_key_pair
%type <data> nxf_long_connective
%type <data> nxf_parameter_list
%type <data> nxf_parameter
%type <data> nxf_key_pair
%type <data> ntf_connective_name
%type <data> ntf_index
%type <data> ntf_short_connective
%type <data> tcf_formula
%type <data> tcf_logic_formula
%type <data> tcf_quantified_formula
%type <data> fof_formula
%type <data> fof_logic_formula
%type <data> fof_binary_formula
%type <data> fof_binary_nonassoc
%type <data> fof_binary_assoc
%type <data> fof_or_formula
%type <data> fof_and_formula
%type <data> fof_unary_formula
%type <data> fof_infix_unary
%type <data> fof_unit_formula
%type <data> fof_unitary_formula
%type <data> fof_quantified_formula
%type <data> fof_variable_list
%type <data> fof_atomic_formula
%type <data> fof_plain_atomic_formula
%type <data> fof_defined_atomic_formula
%type <data> fof_defined_plain_formula
%type <data> fof_defined_infix_formula
%type <data> fof_system_atomic_formula
%type <data> fof_plain_term
%type <data> fof_defined_term
%type <data> fof_defined_atomic_term
%type <data> fof_defined_plain_term
%type <data> fof_system_term
%type <data> fof_arguments
%type <data> fof_term
%type <data> fof_function_term
%type <data> fof_sequent
%type <data> fof_formula_tuple
%type <data> fof_formula_tuple_list
%type <data> comma_fof_logic_formula_list
%type <data> comma_fof_logic_formula
%type <data> cnf_formula
%type <data> cnf_disjunction
%type <data> cnf_literal
%type <data> thf_quantifier
%type <data> thf_unary_connective
%type <data> th0_quantifier
%type <data> type_quantifier
%type <data> subtype_sign
%type <data> tff_unary_connective
%type <data> tff_quantifier
%type <data> fof_quantifier
%type <data> nonassoc_connective
%type <data> assoc_connective
%type <data> unary_connective
%type <data> gentzen_arrow
%type <data> assignment
%type <data> identical
%type <data> type_constant
%type <data> type_functor
%type <data> defined_type
%type <data> atom
%type <data> untyped_atom
%type <data> defined_infix_pred
%type <data> infix_equality
%type <data> infix_inequality
%type <data> constant
%type <data> functor
%type <data> defined_constant
%type <data> defined_functor
%type <data> system_constant
%type <data> system_functor
%type <data> def_or_sys_constant
%type <data> th1_defined_term
%type <data> defined_term
%type <data> variable
%type <data> source
%type <data> sources
%type <data> dag_source
%type <data> inference_record
%type <data> inference_rule
%type <data> internal_source
%type <data> intro_type
%type <data> external_source
%type <data> file_source
%type <data> file_info
%type <data> theory
%type <data> theory_name
%type <data> creator_source
%type <data> creator_name
%type <data> parents
%type <data> parent_list
%type <data> comma_parent_info_list
%type <data> comma_parent_info
%type <data> parent_info
%type <data> parent_details
%type <data> optional_info
%type <data> useful_info
%type <data> include
%type <data> include_optionals
%type <data> formula_selection
%type <data> name_list
%type <data> space_name
%type <data> general_term
%type <data> general_data
%type <data> general_function
%type <data> formula_data
%type <data> general_list
%type <data> general_terms
%type <data> comma_general_term_list
%type <data> comma_general_term
%type <data> name
%type <data> lower_word
%type <data> upper_word
%type <data> single_quoted
%type <data> back_quoted
%type <data> distinct_object
%type <data> atomic_word
%type <data> dollar_word
%type <data> dollar_dollar_word
%type <data> atomic_defined_word
%type <data> atomic_system_word
%type <data> integer
%type <data> rational
%type <data> real
%type <data> number
%type <data> file_name

%destructor { free($$); } <raw>
%destructor { lean_dec($$); } <data>

%start start

%%

start:
  tptp_file { context->result = $1; }
  ;

tptp_file:
  tptp_input_list { $$ = Tptp_mk_TptpFile_mk(lean_array_to_list($1)); }
  ;

tptp_input_list:
  %empty { $$ = lean_mk_empty_array(); }
  | tptp_input_list tptp_input { $$ = lean_array_push($1, $2); }
  ;

tptp_input:
  annotated_formula { $$ = Tptp_mk_TptpInput_annotatedFormula($1); }
  | include { $$ = Tptp_mk_TptpInput_include($1); }
  ;

annotated_formula:
  thf_annotated { $$ = Tptp_mk_AnnotatedFormula_thfAnnotated($1); }
  | tff_annotated { $$ = Tptp_mk_AnnotatedFormula_tffAnnotated($1); }
  | tcf_annotated { $$ = Tptp_mk_AnnotatedFormula_tcfAnnotated($1); }
  | fof_annotated { $$ = Tptp_mk_AnnotatedFormula_fofAnnotated($1); }
  | cnf_annotated { $$ = Tptp_mk_AnnotatedFormula_cnfAnnotated($1); }
  | tpi_annotated { $$ = Tptp_mk_AnnotatedFormula_tpiAnnotated($1); }
  ;

tpi_annotated:
  "tpi(" name "," formula_role "," tpi_formula annotations ")." { $$ = Tptp_mk_TpiAnnotated_mk($2, $4, $6, $7); }
  ;

tpi_formula:
  fof_formula { $$ = Tptp_mk_TpiFormula_mk($1); }
  ;

thf_annotated:
  "thf(" name "," formula_role "," thf_formula annotations ")." { $$ = Tptp_mk_ThfAnnotated_mk($2, $4, $6, $7); }
  ;

tff_annotated:
  "tff(" name "," formula_role "," tff_formula annotations ")." { $$ = Tptp_mk_TffAnnotated_mk($2, $4, $6, $7); }
  ;

tcf_annotated:
  "tcf(" name "," formula_role "," tcf_formula annotations ")." { $$ = Tptp_mk_TcfAnnotated_mk($2, $4, $6, $7); }
  ;

fof_annotated:
  "fof(" name "," formula_role "," fof_formula annotations ")." { $$ = Tptp_mk_FofAnnotated_mk($2, $4, $6, $7); }
  ;

cnf_annotated:
  "cnf(" name "," formula_role "," cnf_formula annotations ")." { $$ = Tptp_mk_CnfAnnotated_mk($2, $4, $6, $7); }
  ;

annotations:
  "," source optional_info { $$ = Tptp_mk_Annotations_sourceOptionalInfo($2, $3); }
  | %empty { $$ = Tptp_mk_Annotations_nothing; }
  ;

formula_role:
  lower_word { $$ = Tptp_mk_FormulaRole_lowerWord($1); }
  | lower_word "-" general_term { $$ = Tptp_mk_FormulaRole_lowerWordGeneralTerm($1, $3); }
  ;

thf_formula:
  thf_logic_formula { $$ = Tptp_mk_ThfFormula_thfLogicFormula($1); }
  | thf_atom_typing { $$ = Tptp_mk_ThfFormula_thfAtomTyping($1); }
  | thf_subtype { $$ = Tptp_mk_ThfFormula_thfSubtype($1); }
  ;

thf_logic_formula:
  thf_unitary_formula { $$ = Tptp_mk_ThfLogicFormula_thfUnitaryFormula($1); }
  | thf_unary_formula { $$ = Tptp_mk_ThfLogicFormula_thfUnaryFormula($1); }
  | thf_binary_formula { $$ = Tptp_mk_ThfLogicFormula_thfBinaryFormula($1); }
  | thf_defined_infix { $$ = Tptp_mk_ThfLogicFormula_thfDefinedInfix($1); }
  | thf_definition { $$ = Tptp_mk_ThfLogicFormula_thfDefinition($1); }
  | thf_sequent { $$ = Tptp_mk_ThfLogicFormula_thfSequent($1); }
  ;

thf_binary_formula:
  thf_binary_nonassoc { $$ = Tptp_mk_ThfBinaryFormula_thfBinaryNonassoc($1); }
  | thf_binary_assoc { $$ = Tptp_mk_ThfBinaryFormula_thfBinaryAssoc($1); }
  | thf_binary_type { $$ = Tptp_mk_ThfBinaryFormula_thfBinaryType($1); }
  ;

thf_binary_nonassoc:
  thf_unit_formula nonassoc_connective thf_unit_formula { $$ = Tptp_mk_ThfBinaryNonassoc_mk($1, $2, $3); }
  ;

thf_binary_assoc:
  thf_or_formula { $$ = Tptp_mk_ThfBinaryAssoc_thfOrFormula($1); }
  | thf_and_formula { $$ = Tptp_mk_ThfBinaryAssoc_thfAndFormula($1); }
  | thf_apply_formula { $$ = Tptp_mk_ThfBinaryAssoc_thfApplyFormula($1); }
  ;

thf_or_formula:
  thf_unit_formula VLINE thf_unit_formula { $$ = Tptp_mk_ThfOrFormula_thfUnitFormulaThfUnitFormula($1, $3); }
  | thf_or_formula VLINE thf_unit_formula { $$ = Tptp_mk_ThfOrFormula_thfOrFormulaThfUnitFormula($1, $3); }
  ;

thf_and_formula:
  thf_unit_formula "&" thf_unit_formula { $$ = Tptp_mk_ThfAndFormula_thfUnitFormulaThfUnitFormula($1, $3); }
  | thf_and_formula "&" thf_unit_formula { $$ = Tptp_mk_ThfAndFormula_thfAndFormulaThfUnitFormula($1, $3); }
  ;

thf_apply_formula:
  thf_unit_formula "@" thf_unit_formula { $$ = Tptp_mk_ThfApplyFormula_thfUnitFormulaThfUnitFormula($1, $3); }
  | thf_apply_formula "@" thf_unit_formula { $$ = Tptp_mk_ThfApplyFormula_thfApplyFormulaThfUnitFormula($1, $3); }
  ;

thf_unit_formula:
  thf_unitary_formula { $$ = Tptp_mk_ThfUnitFormula_thfUnitaryFormula($1); }
  | thf_unary_formula { $$ = Tptp_mk_ThfUnitFormula_thfUnaryFormula($1); }
  | thf_defined_infix { $$ = Tptp_mk_ThfUnitFormula_thfDefinedInfix($1); }
  ;

thf_preunit_formula:
  thf_unitary_formula { $$ = Tptp_mk_ThfPreunitFormula_thfUnitaryFormula($1); }
  | thf_prefix_unary { $$ = Tptp_mk_ThfPreunitFormula_thfPrefixUnary($1); }
  ;

thf_unitary_formula:
  thf_quantified_formula { $$ = Tptp_mk_ThfUnitaryFormula_thfQuantifiedFormula($1); }
  | thf_atomic_formula { $$ = Tptp_mk_ThfUnitaryFormula_thfAtomicFormula($1); }
  | variable { $$ = Tptp_mk_ThfUnitaryFormula_variable($1); }
  | "(" thf_logic_formula ")" { $$ = Tptp_mk_ThfUnitaryFormula_thfLogicFormula($2); }
  ;

thf_quantified_formula:
  thf_quantification thf_unit_formula { $$ = Tptp_mk_ThfQuantifiedFormula_mk($1, $2); }
  ;

thf_quantification:
  thf_quantifier "[" thf_variable_list "]" ":" { $$ = Tptp_mk_ThfQuantification_mk($1, $3); }
  ;

thf_variable_list:
  thf_typed_variable { $$ = Tptp_mk_ThfVariableList_thfTypedVariable($1); }
  | thf_typed_variable "," thf_variable_list { $$ = Tptp_mk_ThfVariableList_thfTypedVariableThfVariableList($1, $3); }
  ;

thf_typed_variable:
  variable ":" thf_top_level_type { $$ = Tptp_mk_ThfTypedVariable_mk($1, $3); }
  ;

thf_unary_formula:
  thf_prefix_unary { $$ = Tptp_mk_ThfUnaryFormula_thfPrefixUnary($1); }
  | thf_infix_unary { $$ = Tptp_mk_ThfUnaryFormula_thfInfixUnary($1); }
  ;

thf_prefix_unary:
  thf_unary_connective thf_preunit_formula { $$ = Tptp_mk_ThfPrefixUnary_mk($1, $2); }
  ;

thf_infix_unary:
  thf_unitary_term infix_inequality thf_unitary_term { $$ = Tptp_mk_ThfInfixUnary_mk($1, $2, $3); }
  ;

thf_atomic_formula:
  thf_plain_atomic { $$ = Tptp_mk_ThfAtomicFormula_thfPlainAtomic($1); }
  | thf_defined_atomic { $$ = Tptp_mk_ThfAtomicFormula_thfDefinedAtomic($1); }
  | thf_system_atomic { $$ = Tptp_mk_ThfAtomicFormula_thfSystemAtomic($1); }
  | thf_fof_function { $$ = Tptp_mk_ThfAtomicFormula_thfFofFunction($1); }
  ;

thf_plain_atomic:
  constant { $$ = Tptp_mk_ThfPlainAtomic_constant($1); }
  | thf_tuple { $$ = Tptp_mk_ThfPlainAtomic_thfTuple($1); }
  ;

thf_defined_atomic:
  defined_constant { $$ = Tptp_mk_ThfDefinedAtomic_definedConstant($1); }
  | thf_defined_term { $$ = Tptp_mk_ThfDefinedAtomic_thfDefinedTerm($1); }
  | "(" thf_conn_term ")" { $$ = Tptp_mk_ThfDefinedAtomic_thfConnTerm($2); }
  | nhf_long_connective { $$ = Tptp_mk_ThfDefinedAtomic_nhfLongConnective($1); }
  | thf_let { $$ = Tptp_mk_ThfDefinedAtomic_thfLet($1); }
  ;

thf_defined_term:
  defined_term { $$ = Tptp_mk_ThfDefinedTerm_definedTerm($1); }
  | th1_defined_term { $$ = Tptp_mk_ThfDefinedTerm_th1DefinedTerm($1); }
  ;

thf_defined_infix:
  thf_unitary_term defined_infix_pred thf_unitary_term { $$ = Tptp_mk_ThfDefinedInfix_mk($1, $2, $3); }
  ;

thf_system_atomic:
  system_constant { $$ = Tptp_mk_ThfSystemAtomic_mk($1); }
  ;

thf_let:
  "$let(" thf_let_types "," thf_let_defns "," thf_logic_formula ")" { $$ = Tptp_mk_ThfLet_mk($2, $4, $6); }
  ;

thf_let_types:
  thf_atom_typing { $$ = Tptp_mk_ThfLetTypes_thfAtomTyping($1); }
  | "[" thf_atom_typing_list "]" { $$ = Tptp_mk_ThfLetTypes_thfAtomTypingList($2); }
  ;

thf_atom_typing_list:
  thf_atom_typing { $$ = Tptp_mk_ThfAtomTypingList_thfAtomTyping($1); }
  | thf_atom_typing "," thf_atom_typing_list { $$ = Tptp_mk_ThfAtomTypingList_thfAtomTypingThfAtomTypingList($1, $3); }
  ;

thf_let_defns:
  thf_let_defn { $$ = Tptp_mk_ThfLetDefns_thfLetDefn($1); }
  | "[" thf_let_defn_list "]" { $$ = Tptp_mk_ThfLetDefns_thfLetDefnList($2); }
  ;

thf_let_defn:
  thf_logic_formula assignment thf_logic_formula { $$ = Tptp_mk_ThfLetDefn_mk($1, $2, $3); }
  ;

thf_let_defn_list:
  thf_let_defn { $$ = Tptp_mk_ThfLetDefnList_thfLetDefn($1); }
  | thf_let_defn "," thf_let_defn_list { $$ = Tptp_mk_ThfLetDefnList_thfLetDefnThfLetDefnList($1, $3); }
  ;

thf_unitary_term:
  thf_atomic_formula { $$ = Tptp_mk_ThfUnitaryTerm_thfAtomicFormula($1); }
  | variable { $$ = Tptp_mk_ThfUnitaryTerm_variable($1); }
  | "(" thf_logic_formula ")" { $$ = Tptp_mk_ThfUnitaryTerm_thfLogicFormula($2); }
  ;

thf_conn_term:
  nonassoc_connective { $$ = Tptp_mk_ThfConnTerm_nonassocConnective($1); }
  | assoc_connective { $$ = Tptp_mk_ThfConnTerm_assocConnective($1); }
  | infix_equality { $$ = Tptp_mk_ThfConnTerm_infixEquality($1); }
  | infix_inequality { $$ = Tptp_mk_ThfConnTerm_infixInequality($1); }
  | thf_unary_connective { $$ = Tptp_mk_ThfConnTerm_thfUnaryConnective($1); }
  ;

thf_tuple:
  "[]" { $$ = Tptp_mk_ThfTuple_empty; }
  | "[" thf_formula_list "]" { $$ = Tptp_mk_ThfTuple_thfFormulaList($2); }
  ;

thf_fof_function:
  functor "(" thf_arguments ")" { $$ = Tptp_mk_ThfFofFunction_functorThfArguments($1, $3); }
  | defined_functor "(" thf_arguments ")" { $$ = Tptp_mk_ThfFofFunction_definedFunctorThfArguments($1, $3); }
  | system_functor "(" thf_arguments ")" { $$ = Tptp_mk_ThfFofFunction_systemFunctorThfArguments($1, $3); }
  ;

thf_arguments:
  thf_formula_list { $$ = Tptp_mk_ThfArguments_mk($1); }
  ;

thf_formula_list:
  thf_logic_formula comma_thf_logic_formula_list { $$ = Tptp_mk_ThfFormulaList_mk($1, lean_array_to_list($2)); }
  ;

comma_thf_logic_formula_list:
  %empty { $$ = lean_mk_empty_array(); }
  | comma_thf_logic_formula_list comma_thf_logic_formula { $$ = lean_array_push($1, $2); }
  ;

comma_thf_logic_formula:
  "," thf_logic_formula { $$ = Tptp_mk_CommaThfLogicFormula_mk($2); }
  ;

thf_atom_typing:
  untyped_atom ":" thf_top_level_type { $$ = Tptp_mk_ThfAtomTyping_untypedAtomThfTopLevelType($1, $3); }
  | "(" thf_atom_typing ")" { $$ = Tptp_mk_ThfAtomTyping_thfAtomTyping($2); }
  ;

thf_top_level_type:
  thf_unitary_type { $$ = Tptp_mk_ThfTopLevelType_thfUnitaryType($1); }
  | thf_mapping_type { $$ = Tptp_mk_ThfTopLevelType_thfMappingType($1); }
  | thf_apply_type { $$ = Tptp_mk_ThfTopLevelType_thfApplyType($1); }
  ;

thf_unitary_type:
  thf_unitary_formula { $$ = Tptp_mk_ThfUnitaryType_mk($1); }
  ;

thf_apply_type:
  thf_apply_formula { $$ = Tptp_mk_ThfApplyType_mk($1); }
  ;

thf_binary_type:
  thf_mapping_type { $$ = Tptp_mk_ThfBinaryType_thfMappingType($1); }
  | thf_xprod_type { $$ = Tptp_mk_ThfBinaryType_thfXprodType($1); }
  | thf_union_type { $$ = Tptp_mk_ThfBinaryType_thfUnionType($1); }
  ;

thf_mapping_type:
  thf_unitary_type ARROW thf_unitary_type { $$ = Tptp_mk_ThfMappingType_thfUnitaryTypeThfUnitaryType($1, $3); }
  | thf_unitary_type ARROW thf_mapping_type { $$ = Tptp_mk_ThfMappingType_thfUnitaryTypeThfMappingType($1, $3); }
  ;

thf_xprod_type:
  thf_unitary_type STAR thf_unitary_type { $$ = Tptp_mk_ThfXprodType_thfUnitaryTypeThfUnitaryType($1, $3); }
  | thf_xprod_type STAR thf_unitary_type { $$ = Tptp_mk_ThfXprodType_thfXprodTypeThfUnitaryType($1, $3); }
  ;

thf_union_type:
  thf_unitary_type PLUS thf_unitary_type { $$ = Tptp_mk_ThfUnionType_thfUnitaryTypeThfUnitaryType($1, $3); }
  | thf_union_type PLUS thf_unitary_type { $$ = Tptp_mk_ThfUnionType_thfUnionTypeThfUnitaryType($1, $3); }
  ;

thf_subtype:
  untyped_atom subtype_sign atom { $$ = Tptp_mk_ThfSubtype_mk($1, $2, $3); }
  ;

thf_definition:
  thf_atomic_formula identical thf_logic_formula { $$ = Tptp_mk_ThfDefinition_mk($1, $2, $3); }
  ;

thf_sequent:
  thf_tuple gentzen_arrow thf_tuple { $$ = Tptp_mk_ThfSequent_mk($1, $2, $3); }
  ;

tff_formula:
  tff_logic_formula { $$ = Tptp_mk_TffFormula_tffLogicFormula($1); }
  | tff_atom_typing { $$ = Tptp_mk_TffFormula_tffAtomTyping($1); }
  | tff_subtype { $$ = Tptp_mk_TffFormula_tffSubtype($1); }
  ;

tff_logic_formula:
  tff_unitary_formula { $$ = Tptp_mk_TffLogicFormula_tffUnitaryFormula($1); }
  | tff_unary_formula { $$ = Tptp_mk_TffLogicFormula_tffUnaryFormula($1); }
  | tff_binary_formula { $$ = Tptp_mk_TffLogicFormula_tffBinaryFormula($1); }
  | tff_defined_infix { $$ = Tptp_mk_TffLogicFormula_tffDefinedInfix($1); }
  | txf_definition { $$ = Tptp_mk_TffLogicFormula_txfDefinition($1); }
  | txf_sequent { $$ = Tptp_mk_TffLogicFormula_txfSequent($1); }
  ;

tff_binary_formula:
  tff_binary_nonassoc { $$ = Tptp_mk_TffBinaryFormula_tffBinaryNonassoc($1); }
  | tff_binary_assoc { $$ = Tptp_mk_TffBinaryFormula_tffBinaryAssoc($1); }
  ;

tff_binary_nonassoc:
  tff_unit_formula nonassoc_connective tff_unit_formula { $$ = Tptp_mk_TffBinaryNonassoc_mk($1, $2, $3); }
  ;

tff_binary_assoc:
  tff_or_formula { $$ = Tptp_mk_TffBinaryAssoc_tffOrFormula($1); }
  | tff_and_formula { $$ = Tptp_mk_TffBinaryAssoc_tffAndFormula($1); }
  ;

tff_or_formula:
  tff_unit_formula VLINE tff_unit_formula { $$ = Tptp_mk_TffOrFormula_tffUnitFormulaTffUnitFormula($1, $3); }
  | tff_or_formula VLINE tff_unit_formula { $$ = Tptp_mk_TffOrFormula_tffOrFormulaTffUnitFormula($1, $3); }
  ;

tff_and_formula:
  tff_unit_formula "&" tff_unit_formula { $$ = Tptp_mk_TffAndFormula_tffUnitFormulaTffUnitFormula($1, $3); }
  | tff_and_formula "&" tff_unit_formula { $$ = Tptp_mk_TffAndFormula_tffAndFormulaTffUnitFormula($1, $3); }
  ;

tff_unit_formula:
  tff_unitary_formula { $$ = Tptp_mk_TffUnitFormula_tffUnitaryFormula($1); }
  | tff_unary_formula { $$ = Tptp_mk_TffUnitFormula_tffUnaryFormula($1); }
  | tff_defined_infix { $$ = Tptp_mk_TffUnitFormula_tffDefinedInfix($1); }
  ;

tff_preunit_formula:
  tff_unitary_formula { $$ = Tptp_mk_TffPreunitFormula_tffUnitaryFormula($1); }
  | tff_prefix_unary { $$ = Tptp_mk_TffPreunitFormula_tffPrefixUnary($1); }
  ;

tff_unitary_formula:
  tff_quantified_formula { $$ = Tptp_mk_TffUnitaryFormula_tffQuantifiedFormula($1); }
  | tff_atomic_formula { $$ = Tptp_mk_TffUnitaryFormula_tffAtomicFormula($1); }
  | txf_unitary_formula { $$ = Tptp_mk_TffUnitaryFormula_txfUnitaryFormula($1); }
  | "(" tff_logic_formula ")" { $$ = Tptp_mk_TffUnitaryFormula_tffLogicFormula($2); }
  ;

txf_unitary_formula:
  variable { $$ = Tptp_mk_TxfUnitaryFormula_mk($1); }
  ;

tff_quantified_formula:
  tff_quantifier "[" tff_variable_list "]" ":" tff_unit_formula { $$ = Tptp_mk_TffQuantifiedFormula_mk($1, $3, $6); }
  ;

tff_variable_list:
  tff_variable { $$ = Tptp_mk_TffVariableList_tffVariable($1); }
  | tff_variable "," tff_variable_list { $$ = Tptp_mk_TffVariableList_tffVariableTffVariableList($1, $3); }
  ;

tff_variable:
  tff_typed_variable { $$ = Tptp_mk_TffVariable_tffTypedVariable($1); }
  | variable { $$ = Tptp_mk_TffVariable_variable($1); }
  ;

tff_typed_variable:
  variable ":" tff_atomic_type { $$ = Tptp_mk_TffTypedVariable_mk($1, $3); }
  ;

tff_unary_formula:
  tff_prefix_unary { $$ = Tptp_mk_TffUnaryFormula_tffPrefixUnary($1); }
  | tff_infix_unary { $$ = Tptp_mk_TffUnaryFormula_tffInfixUnary($1); }
  ;

tff_prefix_unary:
  tff_unary_connective tff_preunit_formula { $$ = Tptp_mk_TffPrefixUnary_mk($1, $2); }
  ;

tff_infix_unary:
  tff_unitary_term infix_inequality tff_unitary_term { $$ = Tptp_mk_TffInfixUnary_mk($1, $2, $3); }
  ;

tff_atomic_formula:
  tff_plain_atomic { $$ = Tptp_mk_TffAtomicFormula_tffPlainAtomic($1); }
  | tff_defined_atomic { $$ = Tptp_mk_TffAtomicFormula_tffDefinedAtomic($1); }
  | tff_system_atomic { $$ = Tptp_mk_TffAtomicFormula_tffSystemAtomic($1); }
  ;

tff_plain_atomic:
  constant { $$ = Tptp_mk_TffPlainAtomic_constant($1); }
  | functor "(" tff_arguments ")" { $$ = Tptp_mk_TffPlainAtomic_functorTffArguments($1, $3); }
  ;

tff_defined_atomic:
  tff_defined_plain { $$ = Tptp_mk_TffDefinedAtomic_mk($1); }
  ;

tff_defined_plain:
  defined_constant { $$ = Tptp_mk_TffDefinedPlain_definedConstant($1); }
  | defined_functor "(" tff_arguments ")" { $$ = Tptp_mk_TffDefinedPlain_definedFunctorTffArguments($1, $3); }
  | nxf_atom { $$ = Tptp_mk_TffDefinedPlain_nxfAtom($1); }
  | txf_let { $$ = Tptp_mk_TffDefinedPlain_txfLet($1); }
  ;

tff_defined_infix:
  tff_unitary_term defined_infix_pred tff_unitary_term { $$ = Tptp_mk_TffDefinedInfix_mk($1, $2, $3); }
  ;

tff_system_atomic:
  system_constant { $$ = Tptp_mk_TffSystemAtomic_systemConstant($1); }
  | system_functor "(" tff_arguments ")" { $$ = Tptp_mk_TffSystemAtomic_systemFunctorTffArguments($1, $3); }
  ;

txf_let:
  "$let(" txf_let_types "," txf_let_defns "," tff_term ")" { $$ = Tptp_mk_TxfLet_mk($2, $4, $6); }
  ;

txf_let_types:
  tff_atom_typing { $$ = Tptp_mk_TxfLetTypes_tffAtomTyping($1); }
  | "[" tff_atom_typing_list "]" { $$ = Tptp_mk_TxfLetTypes_tffAtomTypingList($2); }
  ;

tff_atom_typing_list:
  tff_atom_typing { $$ = Tptp_mk_TffAtomTypingList_tffAtomTyping($1); }
  | tff_atom_typing "," tff_atom_typing_list { $$ = Tptp_mk_TffAtomTypingList_tffAtomTypingTffAtomTypingList($1, $3); }
  ;

txf_let_defns:
  txf_let_defn { $$ = Tptp_mk_TxfLetDefns_txfLetDefn($1); }
  | "[" txf_let_defn_list "]" { $$ = Tptp_mk_TxfLetDefns_txfLetDefnList($2); }
  ;

txf_let_defn:
  txf_let_LHS assignment tff_term { $$ = Tptp_mk_TxfLetDefn_mk($1, $2, $3); }
  ;

txf_let_LHS:
  tff_plain_atomic { $$ = Tptp_mk_TxfLetLHS_tffPlainAtomic($1); }
  | txf_tuple { $$ = Tptp_mk_TxfLetLHS_txfTuple($1); }
  ;

txf_let_defn_list:
  txf_let_defn { $$ = Tptp_mk_TxfLetDefnList_txfLetDefn($1); }
  | txf_let_defn "," txf_let_defn_list { $$ = Tptp_mk_TxfLetDefnList_txfLetDefnTxfLetDefnList($1, $3); }
  ;

nxf_atom:
  nxf_long_connective "@" "(" tff_arguments ")" { $$ = Tptp_mk_NxfAtom_mk($1, $4); }
  ;

tff_term:
  tff_logic_formula { $$ = Tptp_mk_TffTerm_tffLogicFormula($1); }
  | defined_term { $$ = Tptp_mk_TffTerm_definedTerm($1); }
  | txf_tuple { $$ = Tptp_mk_TffTerm_txfTuple($1); }
  ;

tff_unitary_term:
  tff_atomic_formula { $$ = Tptp_mk_TffUnitaryTerm_tffAtomicFormula($1); }
  | defined_term { $$ = Tptp_mk_TffUnitaryTerm_definedTerm($1); }
  | txf_tuple { $$ = Tptp_mk_TffUnitaryTerm_txfTuple($1); }
  | variable { $$ = Tptp_mk_TffUnitaryTerm_variable($1); }
  | "(" tff_logic_formula ")" { $$ = Tptp_mk_TffUnitaryTerm_tffLogicFormula($2); }
  ;

txf_tuple:
  "[]" { $$ = Tptp_mk_TxfTuple_empty; }
  | "[" tff_arguments "]" { $$ = Tptp_mk_TxfTuple_tffArguments($2); }
  ;

tff_arguments:
  tff_term comma_tff_term_list { $$ = Tptp_mk_TffArguments_mk($1, lean_array_to_list($2)); }
  ;

comma_tff_term_list:
  %empty { $$ = lean_mk_empty_array(); }
  | comma_tff_term_list comma_tff_term { $$ = lean_array_push($1, $2); }
  ;

comma_tff_term:
  "," tff_term { $$ = Tptp_mk_CommaTffTerm_mk($2); }
  ;

tff_atom_typing:
  untyped_atom ":" tff_top_level_type { $$ = Tptp_mk_TffAtomTyping_untypedAtomTffTopLevelType($1, $3); }
  | "(" tff_atom_typing ")" { $$ = Tptp_mk_TffAtomTyping_tffAtomTyping($2); }
  ;

tff_top_level_type:
  tff_atomic_type { $$ = Tptp_mk_TffTopLevelType_tffAtomicType($1); }
  | tff_non_atomic_type { $$ = Tptp_mk_TffTopLevelType_tffNonAtomicType($1); }
  ;

tff_non_atomic_type:
  tff_mapping_type { $$ = Tptp_mk_TffNonAtomicType_tffMappingType($1); }
  | tf1_quantified_type { $$ = Tptp_mk_TffNonAtomicType_tf1QuantifiedType($1); }
  | "(" tff_non_atomic_type ")" { $$ = Tptp_mk_TffNonAtomicType_tffNonAtomicType($2); }
  ;

tf1_quantified_type:
  type_quantifier "[" tff_variable_list "]" ":" tff_monotype { $$ = Tptp_mk_Tf1QuantifiedType_mk($1, $3, $6); }
  ;

tff_monotype:
  tff_atomic_type { $$ = Tptp_mk_TffMonotype_tffAtomicType($1); }
  | "(" tff_mapping_type ")" { $$ = Tptp_mk_TffMonotype_tffMappingType($2); }
  | tf1_quantified_type { $$ = Tptp_mk_TffMonotype_tf1QuantifiedType($1); }
  ;

tff_unitary_type:
  tff_atomic_type { $$ = Tptp_mk_TffUnitaryType_tffAtomicType($1); }
  | "(" tff_xprod_type ")" { $$ = Tptp_mk_TffUnitaryType_tffXprodType($2); }
  ;

tff_atomic_type:
  type_constant { $$ = Tptp_mk_TffAtomicType_typeConstant($1); }
  | defined_type { $$ = Tptp_mk_TffAtomicType_definedType($1); }
  | variable { $$ = Tptp_mk_TffAtomicType_variable($1); }
  | type_functor "(" tff_type_arguments ")" { $$ = Tptp_mk_TffAtomicType_typeFunctorTffTypeArguments($1, $3); }
  | "(" tff_atomic_type ")" { $$ = Tptp_mk_TffAtomicType_tffAtomicType($2); }
  | txf_tuple_type { $$ = Tptp_mk_TffAtomicType_txfTupleType($1); }
  ;

tff_type_arguments:
  tff_atomic_type { $$ = Tptp_mk_TffTypeArguments_tffAtomicType($1); }
  | tff_atomic_type "," tff_type_arguments { $$ = Tptp_mk_TffTypeArguments_tffAtomicTypeTffTypeArguments($1, $3); }
  ;

tff_mapping_type:
  tff_unitary_type ARROW tff_atomic_type { $$ = Tptp_mk_TffMappingType_mk($1, $3); }
  ;

tff_xprod_type:
  tff_unitary_type STAR tff_atomic_type { $$ = Tptp_mk_TffXprodType_tffUnitaryTypeTffAtomicType($1, $3); }
  | tff_xprod_type STAR tff_atomic_type { $$ = Tptp_mk_TffXprodType_tffXprodTypeTffAtomicType($1, $3); }
  ;

txf_tuple_type:
  "[" tff_type_list "]" { $$ = Tptp_mk_TxfTupleType_mk($2); }
  ;

tff_type_list:
  tff_top_level_type { $$ = Tptp_mk_TffTypeList_tffTopLevelType($1); }
  | tff_top_level_type "," tff_type_list { $$ = Tptp_mk_TffTypeList_tffTopLevelTypeTffTypeList($1, $3); }
  ;

tff_subtype:
  untyped_atom subtype_sign atom { $$ = Tptp_mk_TffSubtype_mk($1, $2, $3); }
  ;

txf_definition:
  tff_atomic_formula identical tff_term { $$ = Tptp_mk_TxfDefinition_mk($1, $2, $3); }
  ;

txf_sequent:
  txf_tuple gentzen_arrow txf_tuple { $$ = Tptp_mk_TxfSequent_mk($1, $2, $3); }
  ;

nhf_long_connective:
  "{" ntf_connective_name "}" { $$ = Tptp_mk_NhfLongConnective_ntfConnectiveName($2); }
  | "{" ntf_connective_name "(" nhf_parameter_list ")}" { $$ = Tptp_mk_NhfLongConnective_ntfConnectiveNameNhfParameterList($2, $4); }
  ;

nhf_parameter_list:
  nhf_parameter { $$ = Tptp_mk_NhfParameterList_nhfParameter($1); }
  | nhf_parameter "," nhf_parameter_list { $$ = Tptp_mk_NhfParameterList_nhfParameterNhfParameterList($1, $3); }
  ;

nhf_parameter:
  ntf_index { $$ = Tptp_mk_NhfParameter_ntfIndex($1); }
  | nhf_key_pair { $$ = Tptp_mk_NhfParameter_nhfKeyPair($1); }
  ;

nhf_key_pair:
  thf_definition { $$ = Tptp_mk_NhfKeyPair_mk($1); }
  ;

nxf_long_connective:
  "{" ntf_connective_name "}" { $$ = Tptp_mk_NxfLongConnective_ntfConnectiveName($2); }
  | "{" ntf_connective_name "(" nxf_parameter_list ")}" { $$ = Tptp_mk_NxfLongConnective_ntfConnectiveNameNxfParameterList($2, $4); }
  ;

nxf_parameter_list:
  nxf_parameter { $$ = Tptp_mk_NxfParameterList_nxfParameter($1); }
  | nxf_parameter "," nxf_parameter_list { $$ = Tptp_mk_NxfParameterList_nxfParameterNxfParameterList($1, $3); }
  ;

nxf_parameter:
  ntf_index { $$ = Tptp_mk_NxfParameter_ntfIndex($1); }
  | nxf_key_pair { $$ = Tptp_mk_NxfParameter_nxfKeyPair($1); }
  ;

nxf_key_pair:
  txf_definition { $$ = Tptp_mk_NxfKeyPair_mk($1); }
  ;

ntf_connective_name:
  def_or_sys_constant { $$ = Tptp_mk_NtfConnectiveName_mk($1); }
  ;

ntf_index:
  HASH tff_unitary_term { $$ = Tptp_mk_NtfIndex_mk($2); }
  ;

ntf_short_connective:
  "[.]" { $$ = Tptp_mk_NtfShortConnective_bracket; }
  | LESS_SIGN "." ARROW { $$ = Tptp_mk_NtfShortConnective_angle; }
  | "{.}" { $$ = Tptp_mk_NtfShortConnective_brace; }
  | "(.)" { $$ = Tptp_mk_NtfShortConnective_parens; }
  ;

tcf_formula:
  tcf_logic_formula { $$ = Tptp_mk_TcfFormula_tcfLogicFormula($1); }
  | tff_atom_typing { $$ = Tptp_mk_TcfFormula_tffAtomTyping($1); }
  ;

tcf_logic_formula:
  tcf_quantified_formula { $$ = Tptp_mk_TcfLogicFormula_tcfQuantifiedFormula($1); }
  | cnf_formula { $$ = Tptp_mk_TcfLogicFormula_cnfFormula($1); }
  ;

tcf_quantified_formula:
  "!" "[" tff_variable_list "]" ":" tcf_logic_formula { $$ = Tptp_mk_TcfQuantifiedFormula_mk($3, $6); }
  ;

fof_formula:
  fof_logic_formula { $$ = Tptp_mk_FofFormula_fofLogicFormula($1); }
  | fof_sequent { $$ = Tptp_mk_FofFormula_fofSequent($1); }
  ;

fof_logic_formula:
  fof_binary_formula { $$ = Tptp_mk_FofLogicFormula_fofBinaryFormula($1); }
  | fof_unary_formula { $$ = Tptp_mk_FofLogicFormula_fofUnaryFormula($1); }
  | fof_unitary_formula { $$ = Tptp_mk_FofLogicFormula_fofUnitaryFormula($1); }
  ;

fof_binary_formula:
  fof_binary_nonassoc { $$ = Tptp_mk_FofBinaryFormula_fofBinaryNonassoc($1); }
  | fof_binary_assoc { $$ = Tptp_mk_FofBinaryFormula_fofBinaryAssoc($1); }
  ;

fof_binary_nonassoc:
  fof_unit_formula nonassoc_connective fof_unit_formula { $$ = Tptp_mk_FofBinaryNonassoc_mk($1, $2, $3); }
  ;

fof_binary_assoc:
  fof_or_formula { $$ = Tptp_mk_FofBinaryAssoc_fofOrFormula($1); }
  | fof_and_formula { $$ = Tptp_mk_FofBinaryAssoc_fofAndFormula($1); }
  ;

fof_or_formula:
  fof_unit_formula VLINE fof_unit_formula { $$ = Tptp_mk_FofOrFormula_fofUnitFormulaFofUnitFormula($1, $3); }
  | fof_or_formula VLINE fof_unit_formula { $$ = Tptp_mk_FofOrFormula_fofOrFormulaFofUnitFormula($1, $3); }
  ;

fof_and_formula:
  fof_unit_formula "&" fof_unit_formula { $$ = Tptp_mk_FofAndFormula_fofUnitFormulaFofUnitFormula($1, $3); }
  | fof_and_formula "&" fof_unit_formula { $$ = Tptp_mk_FofAndFormula_fofAndFormulaFofUnitFormula($1, $3); }
  ;

fof_unary_formula:
  unary_connective fof_unit_formula { $$ = Tptp_mk_FofUnaryFormula_unaryConnectiveFofUnitFormula($1, $2); }
  | fof_infix_unary { $$ = Tptp_mk_FofUnaryFormula_fofInfixUnary($1); }
  ;

fof_infix_unary:
  fof_term infix_inequality fof_term { $$ = Tptp_mk_FofInfixUnary_mk($1, $2, $3); }
  ;

fof_unit_formula:
  fof_unitary_formula { $$ = Tptp_mk_FofUnitFormula_fofUnitaryFormula($1); }
  | fof_unary_formula { $$ = Tptp_mk_FofUnitFormula_fofUnaryFormula($1); }
  ;

fof_unitary_formula:
  fof_quantified_formula { $$ = Tptp_mk_FofUnitaryFormula_fofQuantifiedFormula($1); }
  | fof_atomic_formula { $$ = Tptp_mk_FofUnitaryFormula_fofAtomicFormula($1); }
  | "(" fof_logic_formula ")" { $$ = Tptp_mk_FofUnitaryFormula_fofLogicFormula($2); }
  ;

fof_quantified_formula:
  fof_quantifier "[" fof_variable_list "]" ":" fof_unit_formula { $$ = Tptp_mk_FofQuantifiedFormula_mk($1, $3, $6); }
  ;

fof_variable_list:
  variable { $$ = Tptp_mk_FofVariableList_variable($1); }
  | variable "," fof_variable_list { $$ = Tptp_mk_FofVariableList_variableFofVariableList($1, $3); }
  ;

fof_atomic_formula:
  fof_plain_atomic_formula { $$ = Tptp_mk_FofAtomicFormula_fofPlainAtomicFormula($1); }
  | fof_defined_atomic_formula { $$ = Tptp_mk_FofAtomicFormula_fofDefinedAtomicFormula($1); }
  | fof_system_atomic_formula { $$ = Tptp_mk_FofAtomicFormula_fofSystemAtomicFormula($1); }
  ;

fof_plain_atomic_formula:
  fof_plain_term { $$ = Tptp_mk_FofPlainAtomicFormula_mk($1); }
  ;

fof_defined_atomic_formula:
  fof_defined_plain_formula { $$ = Tptp_mk_FofDefinedAtomicFormula_fofDefinedPlainFormula($1); }
  | fof_defined_infix_formula { $$ = Tptp_mk_FofDefinedAtomicFormula_fofDefinedInfixFormula($1); }
  ;

fof_defined_plain_formula:
  fof_defined_plain_term { $$ = Tptp_mk_FofDefinedPlainFormula_mk($1); }
  ;

fof_defined_infix_formula:
  fof_term defined_infix_pred fof_term { $$ = Tptp_mk_FofDefinedInfixFormula_mk($1, $2, $3); }
  ;

fof_system_atomic_formula:
  fof_system_term { $$ = Tptp_mk_FofSystemAtomicFormula_mk($1); }
  ;

fof_plain_term:
  constant { $$ = Tptp_mk_FofPlainTerm_constant($1); }
  | functor "(" fof_arguments ")" { $$ = Tptp_mk_FofPlainTerm_functorFofArguments($1, $3); }
  ;

fof_defined_term:
  defined_term { $$ = Tptp_mk_FofDefinedTerm_definedTerm($1); }
  | fof_defined_atomic_term { $$ = Tptp_mk_FofDefinedTerm_fofDefinedAtomicTerm($1); }
  ;

fof_defined_atomic_term:
  fof_defined_plain_term { $$ = Tptp_mk_FofDefinedAtomicTerm_mk($1); }
  ;

fof_defined_plain_term:
  defined_constant { $$ = Tptp_mk_FofDefinedPlainTerm_definedConstant($1); }
  | defined_functor "(" fof_arguments ")" { $$ = Tptp_mk_FofDefinedPlainTerm_definedFunctorFofArguments($1, $3); }
  ;

fof_system_term:
  system_constant { $$ = Tptp_mk_FofSystemTerm_systemConstant($1); }
  | system_functor "(" fof_arguments ")" { $$ = Tptp_mk_FofSystemTerm_systemFunctorFofArguments($1, $3); }
  ;

fof_arguments:
  fof_term { $$ = Tptp_mk_FofArguments_fofTerm($1); }
  | fof_term "," fof_arguments { $$ = Tptp_mk_FofArguments_fofTermFofArguments($1, $3); }
  ;

fof_term:
  fof_function_term { $$ = Tptp_mk_FofTerm_fofFunctionTerm($1); }
  | variable { $$ = Tptp_mk_FofTerm_variable($1); }
  ;

fof_function_term:
  fof_plain_term { $$ = Tptp_mk_FofFunctionTerm_fofPlainTerm($1); }
  | fof_defined_term { $$ = Tptp_mk_FofFunctionTerm_fofDefinedTerm($1); }
  | fof_system_term { $$ = Tptp_mk_FofFunctionTerm_fofSystemTerm($1); }
  ;

fof_sequent:
  fof_formula_tuple gentzen_arrow fof_formula_tuple { $$ = Tptp_mk_FofSequent_fofFormulaTupleGentzenArrowFofFormulaTuple($1, $2, $3); }
  | "(" fof_sequent ")" { $$ = Tptp_mk_FofSequent_fofSequent($2); }
  ;

fof_formula_tuple:
  "[]" { $$ = Tptp_mk_FofFormulaTuple_empty; }
  | "[" fof_formula_tuple_list "]" { $$ = Tptp_mk_FofFormulaTuple_fofFormulaTupleList($2); }
  ;

fof_formula_tuple_list:
  fof_logic_formula comma_fof_logic_formula_list { $$ = Tptp_mk_FofFormulaTupleList_mk($1, lean_array_to_list($2)); }
  ;

comma_fof_logic_formula_list:
  %empty { $$ = lean_mk_empty_array(); }
  | comma_fof_logic_formula_list comma_fof_logic_formula { $$ = lean_array_push($1, $2); }
  ;

comma_fof_logic_formula:
  "," fof_logic_formula { $$ = Tptp_mk_CommaFofLogicFormula_mk($2); }
  ;

cnf_formula:
  cnf_disjunction { $$ = Tptp_mk_CnfFormula_cnfDisjunction($1); }
  | "(" cnf_formula ")" { $$ = Tptp_mk_CnfFormula_cnfFormula($2); }
  ;

cnf_disjunction:
  cnf_literal { $$ = Tptp_mk_CnfDisjunction_cnfLiteral($1); }
  | cnf_disjunction VLINE cnf_literal { $$ = Tptp_mk_CnfDisjunction_cnfDisjunctionCnfLiteral($1, $3); }
  ;

cnf_literal:
  fof_atomic_formula { $$ = Tptp_mk_CnfLiteral_fofAtomicFormula($1); }
  | "~" fof_atomic_formula { $$ = Tptp_mk_CnfLiteral_fofAtomicFormulaNegated($2); }
  | "~" "(" fof_atomic_formula ")" { $$ = Tptp_mk_CnfLiteral_fofAtomicFormulaNegated($3); }
  | fof_infix_unary { $$ = Tptp_mk_CnfLiteral_fofInfixUnary($1); }
  ;

thf_quantifier:
  tff_quantifier { $$ = Tptp_mk_ThfQuantifier_tffQuantifier($1); }
  | th0_quantifier { $$ = Tptp_mk_ThfQuantifier_th0Quantifier($1); }
  | type_quantifier { $$ = Tptp_mk_ThfQuantifier_typeQuantifier($1); }
  ;

thf_unary_connective:
  unary_connective { $$ = Tptp_mk_ThfUnaryConnective_unaryConnective($1); }
  | ntf_short_connective { $$ = Tptp_mk_ThfUnaryConnective_ntfShortConnective($1); }
  ;

th0_quantifier:
  "^" { $$ = Tptp_mk_Th0Quantifier_caret; }
  | "@+" { $$ = Tptp_mk_Th0Quantifier_atPlus; }
  | "@-" { $$ = Tptp_mk_Th0Quantifier_atMinus; }
  ;

type_quantifier:
  "!>" { $$ = Tptp_mk_TypeQuantifier_exclamationArrow; }
  | "?*" { $$ = Tptp_mk_TypeQuantifier_questionStar; }
  ;

subtype_sign:
  "<<" { $$ = Tptp_mk_SubtypeSign_mk; }
  ;

tff_unary_connective:
  unary_connective { $$ = Tptp_mk_TffUnaryConnective_unaryConnective($1); }
  | ntf_short_connective { $$ = Tptp_mk_TffUnaryConnective_ntfShortConnective($1); }
  ;

tff_quantifier:
  fof_quantifier { $$ = Tptp_mk_TffQuantifier_fofQuantifier($1); }
  | HASH { $$ = Tptp_mk_TffQuantifier_hash; }
  ;

fof_quantifier:
  "!" { $$ = Tptp_mk_FofQuantifier_exclamation; }
  | "?" { $$ = Tptp_mk_FofQuantifier_question; }
  ;

nonassoc_connective:
  "<=>" { $$ = Tptp_mk_NonassocConnective_iff; }
  | "=>" { $$ = Tptp_mk_NonassocConnective_fi; }
  | "<=" { $$ = Tptp_mk_NonassocConnective_if; }
  | "<~>" { $$ = Tptp_mk_NonassocConnective_xor; }
  | "~" VLINE { $$ = Tptp_mk_NonassocConnective_nor; }
  | "~&" { $$ = Tptp_mk_NonassocConnective_nand; }
  ;

assoc_connective:
  VLINE { $$ = Tptp_mk_AssocConnective_or; }
  | "&" { $$ = Tptp_mk_AssocConnective_and; }
  ;

unary_connective:
  "~" { $$ = Tptp_mk_UnaryConnective_mk; }
  ;

gentzen_arrow:
  "-->" { $$ = Tptp_mk_GentzenArrow_mk; }
  ;

assignment:
  ":=" { $$ = Tptp_mk_Assignment_mk; }
  ;

identical:
  "==" { $$ = Tptp_mk_Identical_mk; }
  ;

type_constant:
  type_functor { $$ = Tptp_mk_TypeConstant_mk($1); }
  ;

type_functor:
  atomic_word { $$ = Tptp_mk_TypeFunctor_mk($1); }
  ;

defined_type:
  atomic_defined_word { $$ = Tptp_mk_DefinedType_mk($1); }
  ;

atom:
  untyped_atom { $$ = Tptp_mk_Atom_untypedAtom($1); }
  | defined_constant { $$ = Tptp_mk_Atom_definedConstant($1); }
  ;

untyped_atom:
  constant { $$ = Tptp_mk_UntypedAtom_constant($1); }
  | system_constant { $$ = Tptp_mk_UntypedAtom_systemConstant($1); }
  ;

defined_infix_pred:
  infix_equality { $$ = Tptp_mk_DefinedInfixPred_mk($1); }
  ;

infix_equality:
  "=" { $$ = Tptp_mk_InfixEquality_mk; }
  ;

infix_inequality:
  "!=" { $$ = Tptp_mk_InfixInequality_mk; }
  ;

constant:
  functor { $$ = Tptp_mk_Constant_mk($1); }
  ;

functor:
  atomic_word { $$ = Tptp_mk_Functor_mk($1); }
  ;

defined_constant:
  defined_functor { $$ = Tptp_mk_DefinedConstant_mk($1); }
  ;

defined_functor:
  atomic_defined_word { $$ = Tptp_mk_DefinedFunctor_mk($1); }
  ;

system_constant:
  system_functor { $$ = Tptp_mk_SystemConstant_mk($1); }
  ;

system_functor:
  atomic_system_word { $$ = Tptp_mk_SystemFunctor_mk($1); }
  ;

def_or_sys_constant:
  defined_constant { $$ = Tptp_mk_DefOrSysConstant_definedConstant($1); }
  | system_constant { $$ = Tptp_mk_DefOrSysConstant_systemConstant($1); }
  ;

th1_defined_term:
  "!!" { $$ = Tptp_mk_Th1DefinedTerm_doubleExclamation; }
  | "??" { $$ = Tptp_mk_Th1DefinedTerm_doubleQuestion; }
  | "@@+" { $$ = Tptp_mk_Th1DefinedTerm_doubleAtPlus; }
  | "@@-" { $$ = Tptp_mk_Th1DefinedTerm_doubleAtMinus; }
  | "@=" { $$ = Tptp_mk_Th1DefinedTerm_atEquals; }
  ;

distinct_object:
  DISTINCT_OBJECT { $$ = Tptp_mk_DistinctObject_mk(lean_mk_string($1)); free($1); }
  ;

defined_term:
  number { $$ = Tptp_mk_DefinedTerm_number($1); }
  | distinct_object { $$ = Tptp_mk_DefinedTerm_distinctObject($1); }
  ;

upper_word:
  UPPER_WORD { $$ = Tptp_mk_UpperWord_mk(lean_mk_string($1)); free($1); }
  ;

variable:
  upper_word { $$ = Tptp_mk_Variable_mk($1); }
  ;

// There is a reduce-reduce conflict in the grammar that cannot be avoided.
source:
  "unknown" { $$ = Tptp_mk_Source_unknown; }
  | dag_source { $$ = Tptp_mk_Source_dagSource($1); }
  | internal_source { $$ = Tptp_mk_Source_internalSource($1); }
  | external_source { $$ = Tptp_mk_Source_externalSource($1); }
  | "[" sources "]" { $$ = Tptp_mk_Source_sources($2); }
  ;

sources:
  source { $$ = Tptp_mk_Sources_source($1); }
  | source "," sources { $$ = Tptp_mk_Sources_sourceSources($1, $3); }
  ;

dag_source:
  name { $$ = Tptp_mk_DagSource_name($1); }
  | inference_record { $$ = Tptp_mk_DagSource_inferenceRecord($1); }
  ;

inference_record:
  "inference(" inference_rule "," useful_info "," parents ")" { $$ = Tptp_mk_InferenceRecord_mk($2, $4, $6); }
  ;

inference_rule:
  atomic_word { $$ = Tptp_mk_InferenceRule_mk($1); }
  ;

internal_source:
  "introduced(" intro_type "," useful_info "," parents ")" { $$ = Tptp_mk_InternalSource_mk($2, $4, $6); }
  ;

intro_type:
  atomic_word { $$ = Tptp_mk_IntroType_mk($1); }
  ;

external_source:
  file_source { $$ = Tptp_mk_ExternalSource_fileSource($1); }
  | theory { $$ = Tptp_mk_ExternalSource_theory($1); }
  | creator_source { $$ = Tptp_mk_ExternalSource_creatorSource($1); }
  ;

file_source:
  "file(" file_name file_info ")" { $$ = Tptp_mk_FileSource_mk($2, $3); }
  ;

file_info:
  "," name { $$ = Tptp_mk_FileInfo_name($2); }
  | %empty { $$ = Tptp_mk_FileInfo_nothing; }
  ;

theory:
  "theory(" theory_name optional_info ")" { $$ = Tptp_mk_Theory_mk($2, $3); }
  ;

theory_name:
  atomic_word { $$ = Tptp_mk_TheoryName_mk($1); }
  ;

creator_source:
  "creator(" creator_name "," useful_info "," parents ")" { $$ = Tptp_mk_CreatorSource_mk($2, $4, $6); }
  ;

creator_name:
  atomic_word { $$ = Tptp_mk_CreatorName_mk($1); }
  ;

parents:
  "[]" { $$ = Tptp_mk_Parents_empty; }
  | "[" parent_list "]" { $$ = Tptp_mk_Parents_parentList($2); }
  ;

parent_list:
  parent_info comma_parent_info_list { $$ = Tptp_mk_ParentList_mk($1, lean_array_to_list($2)); }
  ;

comma_parent_info_list:
  %empty { $$ = lean_mk_empty_array(); }
  | comma_parent_info_list comma_parent_info { $$ = lean_array_push($1, $2); }
  ;

comma_parent_info:
  "," parent_info { $$ = Tptp_mk_CommaParentInfo_mk($2); }
  ;

parent_info:
  source parent_details { $$ = Tptp_mk_ParentInfo_mk($1, $2); }
  ;

parent_details:
  ":" general_term { $$ = Tptp_mk_ParentDetails_generalTerm($2); }
  | %empty { $$ = Tptp_mk_ParentDetails_nothing; }
  ;

optional_info:
  "," useful_info { $$ = Tptp_mk_OptionalInfo_usefulInfo($2); }
  | %empty { $$ = Tptp_mk_OptionalInfo_nothing; }
  ;

useful_info:
  general_list { $$ = Tptp_mk_UsefulInfo_mk($1); }
  ;

include:
  "include(" file_name include_optionals ")." { $$ = Tptp_mk_Include_mk($2, $3); }
  ;

include_optionals:
  %empty {$$ = Tptp_mk_IncludeOptionals_nothing; }
  | "," formula_selection { $$ = Tptp_mk_IncludeOptionals_formulaSelection($2); }
  | "," formula_selection "," space_name { $$ = Tptp_mk_IncludeOptionals_formulaSelectionSpaceName($2, $4); }
  ;

formula_selection:
  "[" name_list "]" { $$ = Tptp_mk_FormulaSelection_nameList($2); }
  | STAR { $$ = Tptp_mk_FormulaSelection_star; }
  ;

name_list:
  name { $$ = Tptp_mk_NameList_name($1); }
  | name "," name_list { $$ = Tptp_mk_NameList_nameNameList($1, $3); }
  ;

space_name:
  name { $$ = Tptp_mk_SpaceName_mk($1); }
  ;

general_term:
  general_data { $$ = Tptp_mk_GeneralTerm_generalData($1); }
  | general_data ":" general_term { $$ = Tptp_mk_GeneralTerm_generalDataGeneralTerm($1, $3); }
  | general_list { $$ = Tptp_mk_GeneralTerm_generalList($1); }
  ;

general_data:
  atomic_word { $$ = Tptp_mk_GeneralData_atomicWord($1); }
  | general_function { $$ = Tptp_mk_GeneralData_generalFunction($1); }
  | variable { $$ = Tptp_mk_GeneralData_variable($1); }
  | number { $$ = Tptp_mk_GeneralData_number($1); }
  | distinct_object { $$ = Tptp_mk_GeneralData_distinctObject($1); }
  | formula_data { $$ = Tptp_mk_GeneralData_formulaData($1); }
  ;

general_function:
  atomic_word "(" general_terms ")" { $$ = Tptp_mk_GeneralFunction_mk($1, $3); }
  ;

formula_data:
  "$thf(" thf_formula ")" { $$ = Tptp_mk_FormulaData_thfFormula($2); }
  | "$tff(" tff_formula ")" { $$ = Tptp_mk_FormulaData_tffFormula($2); }
  | "$fof(" fof_formula ")" { $$ = Tptp_mk_FormulaData_fofFormula($2); }
  | "$cnf(" cnf_formula ")" { $$ = Tptp_mk_FormulaData_cnfFormula($2); }
  | "$fot(" fof_term ")" { $$ = Tptp_mk_FormulaData_fofTerm($2); }
  ;

general_list:
  "[]" { $$ = Tptp_mk_GeneralList_empty; }
  | "[" general_terms "]" { $$ = Tptp_mk_GeneralList_generalTerms($2); }
  ;

general_terms:
  general_term comma_general_term_list { $$ = Tptp_mk_GeneralTerms_mk($1, lean_array_to_list($2)); }
  ;

comma_general_term_list:
  %empty { $$ = lean_mk_empty_array(); }
  | comma_general_term_list comma_general_term { $$ = lean_array_push($1, $2); }
  ;

comma_general_term:
  "," general_term { $$ = Tptp_mk_CommaGeneralTerm_mk($2); }
  ;

name:
  atomic_word { $$ = Tptp_mk_Name_atomicWord($1); }
  | integer { $$ = Tptp_mk_Name_integer($1); }
  ;

lower_word:
  UNKNOWN { $$ = Tptp_mk_LowerWord_mk(lean_mk_string("unknown")); }
  | LOWER_WORD { $$ = Tptp_mk_LowerWord_mk(lean_mk_string($1)); free($1); }
  ;

single_quoted:
  SINGLE_QUOTED { $$ = Tptp_mk_SingleQuoted_mk(lean_mk_string($1)); free($1); }
  ;

back_quoted:
  BACK_QUOTED { $$ = Tptp_mk_BackQuoted_mk(Tptp_mk_UpperWord_mk(lean_mk_string($1))); free($1); }
  ;

atomic_word:
  lower_word { $$ = Tptp_mk_AtomicWord_lowerWord($1); }
  | single_quoted { $$ = Tptp_mk_AtomicWord_singleQuoted($1); }
  | back_quoted { $$ = Tptp_mk_AtomicWord_backQuoted($1); }
  ;

dollar_word:
  DOLLAR_WORD { $$ = Tptp_mk_DollarWord_mk(lean_mk_string($1)) ; free($1); }
  ;

dollar_dollar_word:
  DOLLAR_DOLLAR_WORD { $$ = Tptp_mk_DollarDollarWord_mk(lean_mk_string($1)); free($1); }
  ;

atomic_defined_word:
  dollar_word { $$ = Tptp_mk_AtomicDefinedWord_mk($1); }
  ;

atomic_system_word:
  dollar_dollar_word { $$ = Tptp_mk_AtomicSystemWord_mk($1); }
  ;

integer:
  INTEGER { $$ = parse_integer($1); free($1); }
  ;

rational:
  RATIONAL { $$ = parse_rational($1); free($1); }
  ;

real:
  REAL { $$ = parse_real($1); free($1); }
  ;

number:
  integer { $$ = Tptp_mk_Number_integer($1); }
  | rational { $$ = Tptp_mk_Number_rational($1); }
  | real { $$ = Tptp_mk_Number_real($1); }
  ;

file_name:
  atomic_word { $$ = Tptp_mk_FileName_mk($1); }
  ;

%%

void yyerror(yyscan_t scanner, TptpParseContext *context, const char *message) {
  (void)scanner;
  (void)message;
  context->error = true;
}
