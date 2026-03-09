#ifndef SBSV_H
#define SBSV_H

#include <stddef.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

#define SBSV_VERSION_MAJOR 0
#define SBSV_VERSION_MINOR 1
#define SBSV_VERSION_PATCH 0

typedef enum {
    SBSV_OK = 0,
    SBSV_ERR_INVALID_ARG = 1,
    SBSV_ERR_ALLOC = 2
} sbsv_status;

typedef struct {
    char** items;
    size_t count;
} sbsv_token_list;

typedef enum {
    SBSV_VALUE_NULL = 0,
    SBSV_VALUE_INT = 1,
    SBSV_VALUE_FLOAT = 2,
    SBSV_VALUE_BOOL = 3,
    SBSV_VALUE_STRING = 4,
    SBSV_VALUE_LIST = 5,
    SBSV_VALUE_CUSTOM = 6
} sbsv_value_type;

typedef enum {
    SBSV_PARSER_DEFAULT = 0,
    SBSV_PARSER_NO_IGNORE_UNKNOWN = 1
} sbsv_parser_flags;

typedef struct sbsv_value sbsv_value;

typedef struct {
    sbsv_value* items;
    size_t count;
} sbsv_value_list;

typedef void (*sbsv_custom_free_fn)(void* ptr);

struct sbsv_value {
    sbsv_value_type type;
    union {
        long long int_value;
        double float_value;
        int bool_value;
        char* string_value;
        sbsv_value_list list;
        void* custom_ptr;
    } data;
    sbsv_custom_free_fn custom_free;
};

typedef struct {
    char* key;
    sbsv_value value;
} sbsv_field;

typedef struct {
    const char* schema_name;
    size_t id;
    sbsv_field* fields;
    size_t field_count;
} sbsv_row;

typedef struct {
    size_t start;
    size_t end;
} sbsv_index_range;

typedef struct sbsv_parser sbsv_parser;

typedef sbsv_status (*sbsv_custom_type_fn)(
    const char* input,
    sbsv_value* out_value,
    void* user_data
);

const char* sbsv_status_str(sbsv_status status);

sbsv_status sbsv_escape_str(const char* input, char** output);
sbsv_status sbsv_unescape_str(const char* input, char** output);

sbsv_status sbsv_tokenize_line(const char* line, sbsv_token_list* out_tokens);
void sbsv_free_token_list(sbsv_token_list* tokens);
void sbsv_free_string(char* value);

void sbsv_value_init(sbsv_value* value);
void sbsv_value_clear(sbsv_value* value);
sbsv_status sbsv_value_set_string(sbsv_value* value, const char* string_value);
sbsv_status sbsv_value_set_custom_ptr(sbsv_value* value, void* custom_ptr, sbsv_custom_free_fn custom_free);

sbsv_parser* sbsv_parser_new(sbsv_parser_flags flags);
void sbsv_parser_free(sbsv_parser* parser);
const char* sbsv_parser_last_error(const sbsv_parser* parser);

sbsv_status sbsv_parser_add_schema(sbsv_parser* parser, const char* schema);
sbsv_status sbsv_parser_add_custom_type(
    sbsv_parser* parser,
    const char* type_name,
    sbsv_custom_type_fn converter,
    void* user_data
);
sbsv_status sbsv_parser_add_group(
    sbsv_parser* parser,
    const char* group_name,
    const char* start_schema,
    const char* end_schema
);
sbsv_status sbsv_parser_parse_line(
    sbsv_parser* parser,
    const char* line,
    size_t line_number
);
sbsv_status sbsv_parser_loads(sbsv_parser* parser, const char* content);
sbsv_status sbsv_parser_load_file(sbsv_parser* parser, FILE* fp);

size_t sbsv_parser_row_count(const sbsv_parser* parser);
const sbsv_row* sbsv_parser_row_at(const sbsv_parser* parser, size_t index);

sbsv_status sbsv_parser_get_rows_in_order(
    const sbsv_parser* parser,
    const char* const* schemas,
    size_t schema_count,
    const sbsv_row*** out_rows,
    size_t* out_count
);
sbsv_status sbsv_parser_get_rows_by_index(
    const sbsv_parser* parser,
    const char* schema,
    sbsv_index_range range,
    const sbsv_row*** out_rows,
    size_t* out_count
);
sbsv_status sbsv_parser_get_rows(
    const sbsv_parser* parser,
    const char* schema,
    const sbsv_row*** out_rows,
    size_t* out_count
);
sbsv_status sbsv_parser_get_group_indices(
    const sbsv_parser* parser,
    const char* group_name,
    sbsv_index_range** out_ranges,
    size_t* out_count
);
void sbsv_free_row_ref_array(const sbsv_row** rows);
void sbsv_free_group_indices(sbsv_index_range* ranges);

const sbsv_value* sbsv_row_get(const sbsv_row* row, const char* key);
const char* sbsv_row_get_string(const sbsv_row* row, const char* key);
long long sbsv_row_get_int(const sbsv_row* row, const char* key, int* valid);
double sbsv_row_get_float(const sbsv_row* row, const char* key, int* valid);
int sbsv_row_get_bool(const sbsv_row* row, const char* key, int* valid);
const sbsv_value_list* sbsv_row_get_list(const sbsv_row* row, const char* key);
void* sbsv_row_get_custom_ptr(const sbsv_row* row, const char* key);

#ifdef __cplusplus
}
#endif

#endif
