#include <limits.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

#include <lean/lean.h>

#include "extern_defs.h"
#include "parser.tab.h"

/* Lean constructor modules have process-wide initializers. They run once;
 * scanner buffers, semantic values, errors, and results are all per-call. */
static pthread_once_t constructors_once = PTHREAD_ONCE_INIT;
static bool constructors_ready = false;

static void initialize_constructors(void) {
  lean_initialize_runtime_module();
  lean_object *result = initialize_tptp__parser_Data(1);
  if (!lean_io_result_is_ok(result)) {
    lean_dec(result);
    return;
  }
  lean_dec_ref(result);
  result = initialize_tptp__parser_Export(1);
  if (!lean_io_result_is_ok(result)) {
    lean_dec(result);
    return;
  }
  lean_dec_ref(result);
  lean_io_mark_end_initialization();
  constructors_ready = true;
}

/* Flex's in-memory buffer API; `yyscan_t` comes from parser.tab.h. */
typedef struct yy_buffer_state *YY_BUFFER_STATE;
YY_BUFFER_STATE yy_scan_bytes(const char *bytes, int length, yyscan_t scanner);
void yy_delete_buffer(YY_BUFFER_STATE buffer, yyscan_t scanner);

static lean_object *initialization_error(void) {
  if (pthread_once(&constructors_once, initialize_constructors) != 0 ||
      !constructors_ready) {
    return lean_io_result_mk_error(lean_mk_string("failed initialization"));
  }
  return NULL;
}

static lean_object *parse_result(TptpParseContext *context, int status) {
  if (context->error || status != 0) {
    if (context->result) lean_dec(context->result);
    return lean_io_result_mk_error(lean_mk_string("parsing failed"));
  }
  return lean_io_result_mk_ok(context->result);
}

/* Each invocation owns a fresh Flex scanner and a pure Bison parse context,
 * with no parser-wide lock. */
LEAN_EXPORT lean_object *Tptp_cparse_parse_file(lean_obj_arg filename) {
  lean_object *error = initialization_error();
  if (error) {
    lean_dec(filename);
    return error;
  }

  FILE *input = fopen(lean_string_cstr(filename), "r");
  lean_dec(filename);
  if (!input) {
    return lean_io_result_mk_error(lean_mk_string("could not open file"));
  }

  TptpParseContext context = { .error = false, .result = NULL };
  yyscan_t scanner;
  if (yylex_init_extra(&context, &scanner) != 0) {
    fclose(input);
    return lean_io_result_mk_error(lean_mk_string("could not initialize scanner"));
  }
  yyset_in(input, scanner);
  int status = yyparse(scanner, &context);
  yylex_destroy(scanner);
  fclose(input);
  return parse_result(&context, status);
}

/* Parse TPTP text held in memory, e.g. a prover's captured stdout. */
LEAN_EXPORT lean_object *Tptp_cparse_parse_string(b_lean_obj_arg text) {
  lean_object *error = initialization_error();
  if (error) return error;

  size_t length = lean_string_size(text) - 1;
  if (length > (size_t)INT_MAX) {
    return lean_io_result_mk_error(lean_mk_string("input too large"));
  }

  TptpParseContext context = { .error = false, .result = NULL };
  yyscan_t scanner;
  if (yylex_init_extra(&context, &scanner) != 0) {
    return lean_io_result_mk_error(lean_mk_string("could not initialize scanner"));
  }
  YY_BUFFER_STATE buffer = yy_scan_bytes(lean_string_cstr(text), (int)length, scanner);
  int status = yyparse(scanner, &context);
  yy_delete_buffer(buffer, scanner);
  yylex_destroy(scanner);
  return parse_result(&context, status);
}
