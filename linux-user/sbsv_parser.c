#include "sbsv.h"

#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    char* name_with_tag;
    char* name;
    char* type_name;
    int nullable;
} sbsv_schema_field;

typedef struct {
    char* name;
    sbsv_schema_field* fields;
    size_t field_count;
    size_t field_capacity;
    sbsv_row** rows;
    size_t row_count;
    size_t row_capacity;
} sbsv_schema;

typedef struct {
    char* name;
    sbsv_custom_type_fn converter;
    void* user_data;
} sbsv_custom_type;

typedef struct {
    char* name;
    size_t start_schema_index;
    size_t end_schema_index;
    sbsv_index_range* ranges;
    size_t range_count;
    size_t range_capacity;
    long long start_index;
} sbsv_group;

struct sbsv_parser {
    int ignore_unknown;
    char* last_error;

    sbsv_schema* schemas;
    size_t schema_count;
    size_t schema_capacity;

    sbsv_custom_type* custom_types;
    size_t custom_type_count;
    size_t custom_type_capacity;

    sbsv_group* groups;
    size_t group_count;
    size_t group_capacity;

    sbsv_row** rows;
    size_t row_count;
    size_t row_capacity;
};

typedef struct {
    char* schema_name;
    char** data_tokens;
    size_t data_count;
    size_t data_capacity;
} sbsv_preprocessed_line;

static void sbsv_parser_set_error(sbsv_parser* parser, const char* format, ...) {
    va_list args;
    va_list copy;
    int needed;
    char* message;

    if (parser == NULL || format == NULL) {
        return;
    }

    free(parser->last_error);
    parser->last_error = NULL;

    va_start(args, format);
    va_copy(copy, args);
    needed = vsnprintf(NULL, 0, format, args);
    va_end(args);
    if (needed < 0) {
        va_end(copy);
        return;
    }

    message = (char*)malloc((size_t)needed + 1);
    if (message == NULL) {
        va_end(copy);
        return;
    }

    vsnprintf(message, (size_t)needed + 1, format, copy);
    va_end(copy);
    parser->last_error = message;
}

static char* sbsv_strdup_local(const char* value) {
    size_t len;
    char* out;

    if (value == NULL) {
        return NULL;
    }

    len = strlen(value);
    out = (char*)malloc(len + 1);
    if (out == NULL) {
        return NULL;
    }

    memcpy(out, value, len + 1);
    return out;
}

static bool sbsv_is_space_char(char ch) {
    return ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' || ch == '\f' || ch == '\v';
}

static void sbsv_trim_inplace(char* value) {
    size_t len;
    size_t start = 0;
    size_t end;

    if (value == NULL) {
        return;
    }

    len = strlen(value);
    while (start < len && sbsv_is_space_char(value[start])) {
        start += 1;
    }

    end = len;
    while (end > start && sbsv_is_space_char(value[end - 1])) {
        end -= 1;
    }

    if (start > 0 && end > start) {
        memmove(value, value + start, end - start);
    } else if (start > 0 && end == start) {
        value[0] = '\0';
        return;
    }

    value[end - start] = '\0';
}

static sbsv_status sbsv_grow_array(void** ptr, size_t elem_size, size_t* capacity, size_t needed) {
    void* new_ptr;
    size_t new_capacity;

    if (needed <= *capacity) {
        return SBSV_OK;
    }

    new_capacity = (*capacity == 0) ? 4 : (*capacity * 2);
    while (new_capacity < needed) {
        new_capacity *= 2;
    }

    new_ptr = realloc(*ptr, elem_size * new_capacity);
    if (new_ptr == NULL) {
        return SBSV_ERR_ALLOC;
    }

    *ptr = new_ptr;
    *capacity = new_capacity;
    return SBSV_OK;
}

void sbsv_value_init(sbsv_value* value) {
    if (value == NULL) {
        return;
    }

    value->type = SBSV_VALUE_NULL;
    value->data.int_value = 0;
    value->custom_free = NULL;
}

void sbsv_value_clear(sbsv_value* value) {
    size_t i;

    if (value == NULL) {
        return;
    }

    if (value->type == SBSV_VALUE_STRING) {
        free(value->data.string_value);
    }

    if (value->type == SBSV_VALUE_LIST) {
        for (i = 0; i < value->data.list.count; ++i) {
            sbsv_value_clear(&value->data.list.items[i]);
        }
        free(value->data.list.items);
    }

    if (value->type == SBSV_VALUE_CUSTOM && value->custom_free != NULL && value->data.custom_ptr != NULL) {
        value->custom_free(value->data.custom_ptr);
    }

    sbsv_value_init(value);
}

sbsv_status sbsv_value_set_string(sbsv_value* value, const char* string_value) {
    char* copy;

    if (value == NULL || string_value == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    copy = sbsv_strdup_local(string_value);
    if (copy == NULL) {
        return SBSV_ERR_ALLOC;
    }

    sbsv_value_clear(value);
    value->type = SBSV_VALUE_STRING;
    value->data.string_value = copy;
    return SBSV_OK;
}

sbsv_status sbsv_value_set_custom_ptr(sbsv_value* value, void* custom_ptr, sbsv_custom_free_fn custom_free) {
    if (value == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    sbsv_value_clear(value);
    value->type = SBSV_VALUE_CUSTOM;
    value->data.custom_ptr = custom_ptr;
    value->custom_free = custom_free;
    return SBSV_OK;
}

static void sbsv_schema_field_free(sbsv_schema_field* field) {
    if (field == NULL) {
        return;
    }
    free(field->name_with_tag);
    free(field->name);
    free(field->type_name);
}

static void sbsv_row_free(sbsv_row* row) {
    size_t i;

    if (row == NULL) {
        return;
    }

    for (i = 0; i < row->field_count; ++i) {
        free(row->fields[i].key);
        sbsv_value_clear(&row->fields[i].value);
    }
    free(row->fields);
    free(row);
}

static void sbsv_schema_free(sbsv_schema* schema) {
    size_t i;

    if (schema == NULL) {
        return;
    }

    free(schema->name);
    for (i = 0; i < schema->field_count; ++i) {
        sbsv_schema_field_free(&schema->fields[i]);
    }
    free(schema->fields);
    free(schema->rows);
}

static void sbsv_group_free(sbsv_group* group) {
    if (group == NULL) {
        return;
    }

    free(group->name);
    free(group->ranges);
}

sbsv_parser* sbsv_parser_new(sbsv_parser_flags flags) {
    sbsv_parser* parser = (sbsv_parser*)calloc(1, sizeof(sbsv_parser));
    if (parser == NULL) {
        return NULL;
    }

    parser->ignore_unknown = (flags & SBSV_PARSER_NO_IGNORE_UNKNOWN) ? 0 : 1;
    return parser;
}

void sbsv_parser_free(sbsv_parser* parser) {
    size_t i;

    if (parser == NULL) {
        return;
    }

    for (i = 0; i < parser->schema_count; ++i) {
        sbsv_schema_free(&parser->schemas[i]);
    }
    free(parser->schemas);

    for (i = 0; i < parser->custom_type_count; ++i) {
        free(parser->custom_types[i].name);
    }
    free(parser->custom_types);

    for (i = 0; i < parser->group_count; ++i) {
        sbsv_group_free(&parser->groups[i]);
    }
    free(parser->groups);

    for (i = 0; i < parser->row_count; ++i) {
        sbsv_row_free(parser->rows[i]);
    }
    free(parser->rows);

    free(parser->last_error);
    free(parser);
}

const char* sbsv_parser_last_error(const sbsv_parser* parser) {
    if (parser == NULL) {
        return "invalid parser";
    }
    return parser->last_error;
}

static sbsv_schema* sbsv_find_schema(sbsv_parser* parser, const char* schema_name) {
    size_t i;
    for (i = 0; i < parser->schema_count; ++i) {
        if (strcmp(parser->schemas[i].name, schema_name) == 0) {
            return &parser->schemas[i];
        }
    }
    return NULL;
}

static const sbsv_schema* sbsv_find_schema_const(const sbsv_parser* parser, const char* schema_name) {
    size_t i;
    for (i = 0; i < parser->schema_count; ++i) {
        if (strcmp(parser->schemas[i].name, schema_name) == 0) {
            return &parser->schemas[i];
        }
    }
    return NULL;
}

static sbsv_custom_type* sbsv_find_custom_type(sbsv_parser* parser, const char* type_name) {
    size_t i;
    for (i = 0; i < parser->custom_type_count; ++i) {
        if (strcmp(parser->custom_types[i].name, type_name) == 0) {
            return &parser->custom_types[i];
        }
    }
    return NULL;
}

static void sbsv_split_token_default(const char* token, char** out_key, char** out_value) {
    const char* cursor;
    size_t key_len;

    *out_key = NULL;
    *out_value = NULL;

    if (token == NULL) {
        return;
    }

    cursor = token;
    while (*cursor != '\0' && !sbsv_is_space_char(*cursor)) {
        cursor += 1;
    }

    key_len = (size_t)(cursor - token);
    *out_key = (char*)malloc(key_len + 1);
    if (*out_key == NULL) {
        return;
    }
    memcpy(*out_key, token, key_len);
    (*out_key)[key_len] = '\0';
    sbsv_trim_inplace(*out_key);

    while (*cursor != '\0' && sbsv_is_space_char(*cursor)) {
        cursor += 1;
    }

    *out_value = sbsv_strdup_local(cursor);
    if (*out_value == NULL) {
        free(*out_key);
        *out_key = NULL;
        return;
    }
    sbsv_trim_inplace(*out_value);
}

static void sbsv_split_token_schema(const char* token, char** out_key, char** out_value) {
    const char* delimiter;
    size_t key_len;

    *out_key = NULL;
    *out_value = NULL;

    if (token == NULL) {
        return;
    }

    delimiter = strchr(token, ':');
    if (delimiter == NULL) {
        *out_key = sbsv_strdup_local(token);
        *out_value = sbsv_strdup_local("");
        if (*out_key != NULL) {
            sbsv_trim_inplace(*out_key);
        }
        if (*out_value != NULL) {
            sbsv_trim_inplace(*out_value);
        }
        return;
    }

    key_len = (size_t)(delimiter - token);
    *out_key = (char*)malloc(key_len + 1);
    if (*out_key == NULL) {
        return;
    }
    memcpy(*out_key, token, key_len);
    (*out_key)[key_len] = '\0';
    sbsv_trim_inplace(*out_key);

    *out_value = sbsv_strdup_local(delimiter + 1);
    if (*out_value == NULL) {
        free(*out_key);
        *out_key = NULL;
        return;
    }
    sbsv_trim_inplace(*out_value);
}

static sbsv_status sbsv_schema_add_field(sbsv_schema* schema, sbsv_schema_field field) {
    sbsv_status status = sbsv_grow_array((void**)&schema->fields, sizeof(sbsv_schema_field), &schema->field_capacity, schema->field_count + 1);
    if (status != SBSV_OK) {
        return status;
    }

    schema->fields[schema->field_count] = field;
    schema->field_count += 1;
    return SBSV_OK;
}

static sbsv_status sbsv_schema_push_row(sbsv_schema* schema, sbsv_row* row) {
    sbsv_status status = sbsv_grow_array((void**)&schema->rows, sizeof(sbsv_row*), &schema->row_capacity, schema->row_count + 1);
    if (status != SBSV_OK) {
        return status;
    }
    schema->rows[schema->row_count] = row;
    schema->row_count += 1;
    return SBSV_OK;
}

static sbsv_status sbsv_parser_push_row(sbsv_parser* parser, sbsv_row* row) {
    sbsv_status status = sbsv_grow_array((void**)&parser->rows, sizeof(sbsv_row*), &parser->row_capacity, parser->row_count + 1);
    if (status != SBSV_OK) {
        return status;
    }
    parser->rows[parser->row_count] = row;
    parser->row_count += 1;
    return SBSV_OK;
}

static sbsv_status sbsv_parser_add_schema_name_suffix(char** name, const char* suffix) {
    size_t old_len;
    size_t suffix_len;
    char* out;

    old_len = strlen(*name);
    suffix_len = strlen(suffix);
    out = (char*)malloc(old_len + 1 + suffix_len + 1);
    if (out == NULL) {
        return SBSV_ERR_ALLOC;
    }

    memcpy(out, *name, old_len);
    out[old_len] = '$';
    memcpy(out + old_len + 1, suffix, suffix_len + 1);
    free(*name);
    *name = out;
    return SBSV_OK;
}

sbsv_status sbsv_parser_add_schema(sbsv_parser* parser, const char* schema_expr) {
    sbsv_token_list tokens;
    sbsv_schema parsed;
    size_t i;
    sbsv_status status;

    if (parser == NULL || schema_expr == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    memset(&tokens, 0, sizeof(tokens));
    memset(&parsed, 0, sizeof(parsed));

    status = sbsv_tokenize_line(schema_expr, &tokens);
    if (status != SBSV_OK) {
        sbsv_parser_set_error(parser, "Invalid schema: failed to tokenize");
        return status;
    }

    if (tokens.count == 0) {
        sbsv_parser_set_error(parser, "Invalid schema %s: too short", schema_expr);
        sbsv_free_token_list(&tokens);
        return SBSV_ERR_INVALID_ARG;
    }

    parsed.name = sbsv_strdup_local(tokens.items[0]);
    if (parsed.name == NULL) {
        sbsv_free_token_list(&tokens);
        return SBSV_ERR_ALLOC;
    }

    for (i = 1; i < tokens.count; ++i) {
        char* key = NULL;
        char* value = NULL;
        sbsv_schema_field field;

        memset(&field, 0, sizeof(field));
        sbsv_split_token_default(tokens.items[i], &key, &value);
        if (key == NULL || value == NULL) {
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_ALLOC;
        }

        if (strlen(key) == 0) {
            sbsv_parser_set_error(parser, "Invalid schema %s: empty name", tokens.items[i]);
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
        }

        if (strlen(value) == 0) {
            status = sbsv_parser_add_schema_name_suffix(&parsed.name, key);
            free(key);
            free(value);
            if (status != SBSV_OK) {
                sbsv_schema_free(&parsed);
                sbsv_free_token_list(&tokens);
                return status;
            }
            continue;
        }

        free(key);
        free(value);

        sbsv_split_token_schema(tokens.items[i], &key, &value);
        if (key == NULL || value == NULL) {
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_ALLOC;
        }

        field.nullable = 0;
        if (strlen(key) > 0 && key[strlen(key) - 1] == '?') {
            key[strlen(key) - 1] = '\0';
            field.nullable = 1;
        }

        field.name_with_tag = sbsv_strdup_local(key);
        field.type_name = sbsv_strdup_local(value);
        if (field.name_with_tag == NULL || field.type_name == NULL) {
            free(key);
            free(value);
            sbsv_schema_field_free(&field);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_ALLOC;
        }

        {
            const char* dollar = strchr(field.name_with_tag, '$');
            if (dollar != NULL) {
                size_t base_len = (size_t)(dollar - field.name_with_tag);
                field.name = (char*)malloc(base_len + 1);
                if (field.name == NULL) {
                    free(key);
                    free(value);
                    sbsv_schema_field_free(&field);
                    sbsv_schema_free(&parsed);
                    sbsv_free_token_list(&tokens);
                    return SBSV_ERR_ALLOC;
                }
                memcpy(field.name, field.name_with_tag, base_len);
                field.name[base_len] = '\0';
            } else {
                field.name = sbsv_strdup_local(field.name_with_tag);
                if (field.name == NULL) {
                    free(key);
                    free(value);
                    sbsv_schema_field_free(&field);
                    sbsv_schema_free(&parsed);
                    sbsv_free_token_list(&tokens);
                    return SBSV_ERR_ALLOC;
                }
            }
        }

        free(key);
        free(value);

        status = sbsv_schema_add_field(&parsed, field);
        if (status != SBSV_OK) {
            sbsv_schema_field_free(&field);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return status;
        }
    }

    status = sbsv_grow_array((void**)&parser->schemas, sizeof(sbsv_schema), &parser->schema_capacity, parser->schema_count + 1);
    if (status != SBSV_OK) {
        sbsv_schema_free(&parsed);
        sbsv_free_token_list(&tokens);
        return status;
    }

    {
        sbsv_schema* existing = sbsv_find_schema(parser, parsed.name);
        if (existing != NULL) {
            sbsv_schema_free(existing);
            *existing = parsed;
        } else {
            parser->schemas[parser->schema_count] = parsed;
            parser->schema_count += 1;
        }
    }

    sbsv_free_token_list(&tokens);
    return SBSV_OK;
}

sbsv_status sbsv_parser_add_custom_type(
    sbsv_parser* parser,
    const char* type_name,
    sbsv_custom_type_fn converter,
    void* user_data
) {
    sbsv_custom_type* existing;
    sbsv_status status;

    if (parser == NULL || type_name == NULL || converter == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    existing = sbsv_find_custom_type(parser, type_name);
    if (existing != NULL) {
        existing->converter = converter;
        existing->user_data = user_data;
        return SBSV_OK;
    }

    status = sbsv_grow_array((void**)&parser->custom_types, sizeof(sbsv_custom_type), &parser->custom_type_capacity, parser->custom_type_count + 1);
    if (status != SBSV_OK) {
        return status;
    }

    parser->custom_types[parser->custom_type_count].name = sbsv_strdup_local(type_name);
    if (parser->custom_types[parser->custom_type_count].name == NULL) {
        return SBSV_ERR_ALLOC;
    }
    parser->custom_types[parser->custom_type_count].converter = converter;
    parser->custom_types[parser->custom_type_count].user_data = user_data;
    parser->custom_type_count += 1;
    return SBSV_OK;
}

static int sbsv_schema_need_parsing(const char* schema_name) {
    size_t len;
    if (schema_name == NULL) {
        return 0;
    }
    len = strlen(schema_name);
    return len >= 2 && schema_name[0] == '[' && schema_name[len - 1] == ']';
}

static sbsv_status sbsv_schema_name_from_expr(const char* schema_expr, char** out_name) {
    sbsv_token_list tokens;
    char* name;
    size_t i;
    sbsv_status status;

    *out_name = NULL;

    if (!sbsv_schema_need_parsing(schema_expr)) {
        *out_name = sbsv_strdup_local(schema_expr);
        return (*out_name == NULL) ? SBSV_ERR_ALLOC : SBSV_OK;
    }

    memset(&tokens, 0, sizeof(tokens));
    status = sbsv_tokenize_line(schema_expr, &tokens);
    if (status != SBSV_OK) {
        return status;
    }

    if (tokens.count == 0) {
        sbsv_free_token_list(&tokens);
        return SBSV_ERR_INVALID_ARG;
    }

    name = sbsv_strdup_local(tokens.items[0]);
    if (name == NULL) {
        sbsv_free_token_list(&tokens);
        return SBSV_ERR_ALLOC;
    }

    for (i = 1; i < tokens.count; ++i) {
        char* key = NULL;
        char* value = NULL;
        sbsv_status add_status;

        sbsv_split_token_default(tokens.items[i], &key, &value);
        if (key == NULL || value == NULL) {
            free(key);
            free(value);
            free(name);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_ALLOC;
        }

        if (strlen(value) == 0) {
            add_status = sbsv_parser_add_schema_name_suffix(&name, key);
            free(key);
            free(value);
            if (add_status != SBSV_OK) {
                free(name);
                sbsv_free_token_list(&tokens);
                return add_status;
            }
        } else {
            free(key);
            free(value);
            break;
        }
    }

    sbsv_free_token_list(&tokens);
    *out_name = name;
    return SBSV_OK;
}

sbsv_status sbsv_parser_add_group(
    sbsv_parser* parser,
    const char* group_name,
    const char* start_schema,
    const char* end_schema
) {
    sbsv_group group;
    sbsv_schema* start;
    sbsv_schema* end;
    size_t start_index;
    size_t end_index;
    char* start_name = NULL;
    char* end_name = NULL;
    sbsv_status status;

    if (parser == NULL || group_name == NULL || start_schema == NULL || end_schema == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    status = sbsv_schema_name_from_expr(start_schema, &start_name);
    if (status != SBSV_OK) {
        return status;
    }
    status = sbsv_schema_name_from_expr(end_schema, &end_name);
    if (status != SBSV_OK) {
        free(start_name);
        return status;
    }

    start = sbsv_find_schema(parser, start_name);
    end = sbsv_find_schema(parser, end_name);
    if (start == NULL || end == NULL) {
        sbsv_parser_set_error(parser, "Invalid group schema: start=%s end=%s", start_name, end_name);
        free(start_name);
        free(end_name);
        return SBSV_ERR_INVALID_ARG;
    }

    start_index = (size_t)(start - parser->schemas);
    end_index = (size_t)(end - parser->schemas);

    memset(&group, 0, sizeof(group));
    group.name = sbsv_strdup_local(group_name);
    if (group.name == NULL) {
        free(start_name);
        free(end_name);
        return SBSV_ERR_ALLOC;
    }
    group.start_schema_index = start_index;
    group.end_schema_index = end_index;
    group.start_index = -1;

    status = sbsv_grow_array((void**)&parser->groups, sizeof(sbsv_group), &parser->group_capacity, parser->group_count + 1);
    if (status != SBSV_OK) {
        free(group.name);
        free(start_name);
        free(end_name);
        return status;
    }

    parser->groups[parser->group_count] = group;
    parser->group_count += 1;
    free(start_name);
    free(end_name);
    return SBSV_OK;
}

static sbsv_status sbsv_parse_value(
    sbsv_parser* parser,
    const char* type_name,
    const char* raw,
    sbsv_value* out_value
);

static int sbsv_parse_bool(const char* value, int* out_bool) {
    char lowered[16];
    size_t len = strlen(value);
    size_t i;
    if (len >= sizeof(lowered)) {
        return 0;
    }
    for (i = 0; i < len; ++i) {
        lowered[i] = (char)tolower((unsigned char)value[i]);
    }
    lowered[len] = '\0';

    if (strcmp(lowered, "t") == 0 || strcmp(lowered, "true") == 0 || strcmp(lowered, "y") == 0 || strcmp(lowered, "yes") == 0 || strcmp(lowered, "1") == 0) {
        *out_bool = 1;
        return 1;
    }
    if (strcmp(lowered, "f") == 0 || strcmp(lowered, "false") == 0 || strcmp(lowered, "n") == 0 || strcmp(lowered, "no") == 0 || strcmp(lowered, "0") == 0) {
        *out_bool = 0;
        return 1;
    }
    return 0;
}

static sbsv_status sbsv_parse_list_value(
    sbsv_parser* parser,
    const char* type_name,
    const char* raw,
    sbsv_value* out_value
) {
    sbsv_token_list list_tokens;
    char* subtype;
    size_t subtype_len;
    size_t i;
    sbsv_status status;

    memset(&list_tokens, 0, sizeof(list_tokens));

    subtype_len = strlen(type_name);
    if (subtype_len < 7 || strncmp(type_name, "list[", 5) != 0 || type_name[subtype_len - 1] != ']') {
        return SBSV_ERR_INVALID_ARG;
    }

    subtype = (char*)malloc(subtype_len - 5);
    if (subtype == NULL) {
        return SBSV_ERR_ALLOC;
    }
    memcpy(subtype, type_name + 5, subtype_len - 6);
    subtype[subtype_len - 6] = '\0';

    status = sbsv_tokenize_line(raw, &list_tokens);
    if (status != SBSV_OK) {
        free(subtype);
        return status;
    }

    out_value->type = SBSV_VALUE_LIST;
    out_value->data.list.count = list_tokens.count;
    out_value->data.list.items = (sbsv_value*)calloc(list_tokens.count, sizeof(sbsv_value));
    if (list_tokens.count > 0 && out_value->data.list.items == NULL) {
        free(subtype);
        sbsv_free_token_list(&list_tokens);
        return SBSV_ERR_ALLOC;
    }

    for (i = 0; i < list_tokens.count; ++i) {
        sbsv_value_init(&out_value->data.list.items[i]);
        status = sbsv_parse_value(parser, subtype, list_tokens.items[i], &out_value->data.list.items[i]);
        if (status != SBSV_OK) {
            free(subtype);
            sbsv_free_token_list(&list_tokens);
            return status;
        }
    }

    free(subtype);
    sbsv_free_token_list(&list_tokens);
    return SBSV_OK;
}

static sbsv_status sbsv_parse_value(
    sbsv_parser* parser,
    const char* type_name,
    const char* raw,
    sbsv_value* out_value
) {
    char* end_ptr;
    sbsv_custom_type* custom;

    if (strcmp(type_name, "int") == 0) {
        long long parsed;
        errno = 0;
        parsed = strtoll(raw, &end_ptr, 10);
        if (errno != 0 || *end_ptr != '\0') {
            sbsv_parser_set_error(parser, "Invalid int value: %s", raw);
            return SBSV_ERR_INVALID_ARG;
        }
        out_value->type = SBSV_VALUE_INT;
        out_value->data.int_value = parsed;
        return SBSV_OK;
    }

    if (strcmp(type_name, "float") == 0) {
        double parsed;
        errno = 0;
        parsed = strtod(raw, &end_ptr);
        if (errno != 0 || *end_ptr != '\0') {
            sbsv_parser_set_error(parser, "Invalid float value: %s", raw);
            return SBSV_ERR_INVALID_ARG;
        }
        out_value->type = SBSV_VALUE_FLOAT;
        out_value->data.float_value = parsed;
        return SBSV_OK;
    }

    if (strcmp(type_name, "str") == 0) {
        return sbsv_value_set_string(out_value, raw);
    }

    if (strcmp(type_name, "bool") == 0) {
        int bool_value;
        if (!sbsv_parse_bool(raw, &bool_value)) {
            sbsv_parser_set_error(parser, "Invalid boolean value: %s", raw);
            return SBSV_ERR_INVALID_ARG;
        }
        out_value->type = SBSV_VALUE_BOOL;
        out_value->data.bool_value = bool_value;
        return SBSV_OK;
    }

    if (strncmp(type_name, "list[", 5) == 0) {
        return sbsv_parse_list_value(parser, type_name, raw, out_value);
    }

    custom = sbsv_find_custom_type(parser, type_name);
    if (custom != NULL) {
        return custom->converter(raw, out_value, custom->user_data);
    }

    return sbsv_value_set_string(out_value, raw);
}

static sbsv_status sbsv_preprocess_line(const char* line, sbsv_preprocessed_line* out_line) {
    sbsv_token_list tokens;
    size_t i;
    int may_have_sub_schema = 1;
    sbsv_status status;

    memset(out_line, 0, sizeof(*out_line));
    memset(&tokens, 0, sizeof(tokens));

    status = sbsv_tokenize_line(line, &tokens);
    if (status != SBSV_OK) {
        return status;
    }

    for (i = 0; i < tokens.count; ++i) {
        char* key = NULL;
        char* value = NULL;

        sbsv_split_token_default(tokens.items[i], &key, &value);
        if (key == NULL || value == NULL) {
            free(key);
            free(value);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_ALLOC;
        }

        if (strlen(key) > 0 && strlen(value) == 0 && may_have_sub_schema) {
            if (out_line->schema_name == NULL) {
                out_line->schema_name = sbsv_strdup_local(key);
                if (out_line->schema_name == NULL) {
                    free(key);
                    free(value);
                    sbsv_free_token_list(&tokens);
                    return SBSV_ERR_ALLOC;
                }
            } else {
                sbsv_status append_status = sbsv_parser_add_schema_name_suffix(&out_line->schema_name, key);
                if (append_status != SBSV_OK) {
                    free(key);
                    free(value);
                    sbsv_free_token_list(&tokens);
                    return append_status;
                }
            }
        } else {
            char* copied = sbsv_strdup_local(tokens.items[i]);
            sbsv_status grow_status;
            may_have_sub_schema = 0;
            if (copied == NULL) {
                free(key);
                free(value);
                sbsv_free_token_list(&tokens);
                return SBSV_ERR_ALLOC;
            }

            grow_status = sbsv_grow_array((void**)&out_line->data_tokens, sizeof(char*), &out_line->data_capacity, out_line->data_count + 1);
            if (grow_status != SBSV_OK) {
                free(copied);
                free(key);
                free(value);
                sbsv_free_token_list(&tokens);
                return grow_status;
            }

            out_line->data_tokens[out_line->data_count] = copied;
            out_line->data_count += 1;
        }

        free(key);
        free(value);
    }

    sbsv_free_token_list(&tokens);
    return SBSV_OK;
}

static void sbsv_preprocessed_line_free(sbsv_preprocessed_line* pre) {
    size_t i;
    if (pre == NULL) {
        return;
    }
    free(pre->schema_name);
    for (i = 0; i < pre->data_count; ++i) {
        free(pre->data_tokens[i]);
    }
    free(pre->data_tokens);
    memset(pre, 0, sizeof(*pre));
}

static sbsv_status sbsv_group_add_range(sbsv_group* group, sbsv_index_range range) {
    sbsv_status status = sbsv_grow_array((void**)&group->ranges, sizeof(sbsv_index_range), &group->range_capacity, group->range_count + 1);
    if (status != SBSV_OK) {
        return status;
    }
    group->ranges[group->range_count] = range;
    group->range_count += 1;
    return SBSV_OK;
}

static sbsv_status sbsv_parser_append_row(sbsv_parser* parser, sbsv_schema* schema, sbsv_row* row) {
    size_t current_id = parser->row_count;
    size_t schema_index;
    size_t i;
    sbsv_status status;

    if (schema < parser->schemas || schema >= parser->schemas + parser->schema_count) {
        return SBSV_ERR_INVALID_ARG;
    }
    schema_index = (size_t)(schema - parser->schemas);

    row->id = current_id;
    row->schema_name = schema->name;

    status = sbsv_schema_push_row(schema, row);
    if (status != SBSV_OK) {
        return status;
    }
    status = sbsv_parser_push_row(parser, row);
    if (status != SBSV_OK) {
        schema->row_count -= 1;
        return status;
    }

    for (i = 0; i < parser->group_count; ++i) {
        sbsv_group* group = &parser->groups[i];
        if (group->end_schema_index == schema_index && group->start_index >= 0) {
            sbsv_index_range range;
            if (group->start_schema_index == schema_index) {
                if (current_id == 0) {
                    range.start = 0;
                    range.end = 0;
                } else {
                    range.start = (size_t)group->start_index;
                    range.end = current_id - 1;
                }
            } else {
                range.start = (size_t)group->start_index;
                range.end = current_id;
            }
            status = sbsv_group_add_range(group, range);
            if (status != SBSV_OK) {
                return status;
            }
            group->start_index = -1;
        }
    }

    for (i = 0; i < parser->group_count; ++i) {
        sbsv_group* group = &parser->groups[i];
        if (group->start_schema_index == schema_index && group->start_index < 0) {
            group->start_index = (long long)current_id;
        }
    }

    return SBSV_OK;
}

static sbsv_status sbsv_parse_row_for_schema(
    sbsv_parser* parser,
    sbsv_schema* schema,
    char** tokens,
    size_t token_count,
    sbsv_row** out_row
) {
    sbsv_row* row;
    size_t field_index;
    size_t queue_index = 0;

    if (token_count < schema->field_count) {
        sbsv_parser_set_error(parser, "Invalid data: too short");
        return SBSV_ERR_INVALID_ARG;
    }

    row = (sbsv_row*)calloc(1, sizeof(sbsv_row));
    if (row == NULL) {
        return SBSV_ERR_ALLOC;
    }
    row->field_count = schema->field_count;
    row->fields = (sbsv_field*)calloc(schema->field_count, sizeof(sbsv_field));
    if (row->fields == NULL) {
        free(row);
        return SBSV_ERR_ALLOC;
    }

    for (field_index = 0; field_index < schema->field_count; ++field_index) {
        sbsv_schema_field* field = &schema->fields[field_index];
        int matched = 0;

        row->fields[field_index].key = sbsv_strdup_local(field->name_with_tag);
        if (row->fields[field_index].key == NULL) {
            sbsv_row_free(row);
            return SBSV_ERR_ALLOC;
        }
        sbsv_value_init(&row->fields[field_index].value);

        while (queue_index < token_count) {
            char* key = NULL;
            char* value = NULL;
            sbsv_status convert_status;
            sbsv_split_token_default(tokens[queue_index], &key, &value);
            queue_index += 1;

            if (key == NULL || value == NULL) {
                free(key);
                free(value);
                sbsv_row_free(row);
                return SBSV_ERR_ALLOC;
            }

            if (strlen(key) == 0) {
                free(key);
                free(value);
                sbsv_parser_set_error(parser, "Invalid data %s: empty name", tokens[queue_index - 1]);
                sbsv_row_free(row);
                return SBSV_ERR_INVALID_ARG;
            }

            if (strcmp(field->name, key) != 0) {
                free(key);
                free(value);
                continue;
            }

            if (strlen(value) == 0 && field->nullable) {
                row->fields[field_index].value.type = SBSV_VALUE_NULL;
                matched = 1;
                free(key);
                free(value);
                break;
            }

            if (strlen(value) == 0 && !field->nullable) {
                free(key);
                free(value);
                sbsv_parser_set_error(parser, "Invalid data %s: empty value", tokens[queue_index - 1]);
                sbsv_row_free(row);
                return SBSV_ERR_INVALID_ARG;
            }

            convert_status = sbsv_parse_value(parser, field->type_name, value, &row->fields[field_index].value);
            free(key);
            free(value);
            if (convert_status != SBSV_OK) {
                sbsv_row_free(row);
                return convert_status;
            }
            matched = 1;
            break;
        }

        if (!matched) {
            sbsv_parser_set_error(parser, "Invalid data: missing key");
            sbsv_row_free(row);
            return SBSV_ERR_INVALID_ARG;
        }
    }

    *out_row = row;
    return SBSV_OK;
}

sbsv_status sbsv_parser_parse_line(sbsv_parser* parser, const char* line, size_t line_number) {
    char* stripped;
    sbsv_preprocessed_line pre;
    sbsv_schema* schema;
    sbsv_row* row = NULL;
    sbsv_status status;

    if (parser == NULL || line == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    stripped = sbsv_strdup_local(line);
    if (stripped == NULL) {
        return SBSV_ERR_ALLOC;
    }
    sbsv_trim_inplace(stripped);

    if (stripped[0] == '\0' || stripped[0] == '#') {
        free(stripped);
        return SBSV_OK;
    }

    status = sbsv_preprocess_line(stripped, &pre);
    free(stripped);
    if (status != SBSV_OK) {
        return status;
    }

    if (pre.schema_name == NULL) {
        if (parser->ignore_unknown) {
            sbsv_preprocessed_line_free(&pre);
            return SBSV_OK;
        }
        sbsv_parser_set_error(parser, "Parse error (line=%zu, schema=<none>): Invalid schema <none> at line %zu", line_number, line_number);
        sbsv_preprocessed_line_free(&pre);
        return SBSV_ERR_INVALID_ARG;
    }

    schema = sbsv_find_schema(parser, pre.schema_name);
    if (schema == NULL) {
        if (parser->ignore_unknown) {
            sbsv_preprocessed_line_free(&pre);
            return SBSV_OK;
        }
        sbsv_parser_set_error(parser, "Parse error (line=%zu, schema=%s): Invalid schema %s at line %zu", line_number, pre.schema_name, pre.schema_name, line_number);
        sbsv_preprocessed_line_free(&pre);
        return SBSV_ERR_INVALID_ARG;
    }

    status = sbsv_parse_row_for_schema(parser, schema, pre.data_tokens, pre.data_count, &row);
    if (status != SBSV_OK) {
        const char* detail = parser->last_error ? parser->last_error : "parse error";
        char* detail_copy = sbsv_strdup_local(detail);
        if (detail_copy != NULL) {
            sbsv_parser_set_error(parser, "Parse error (line=%zu, schema=%s): %s", line_number, schema->name, detail_copy);
            free(detail_copy);
        } else {
            sbsv_parser_set_error(parser, "Parse error (line=%zu, schema=%s): parse error", line_number, schema->name);
        }
        sbsv_preprocessed_line_free(&pre);
        return status;
    }

    status = sbsv_parser_append_row(parser, schema, row);
    if (status != SBSV_OK) {
        sbsv_row_free(row);
    }

    sbsv_preprocessed_line_free(&pre);
    return status;
}

sbsv_status sbsv_parser_loads(sbsv_parser* parser, const char* content) {
    const char* cursor;
    const char* line_start;
    size_t line_number = 1;

    if (parser == NULL || content == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    cursor = content;
    line_start = content;
    size_t prev_line_len = 0;
    char* line_buffer = NULL;
    while (1) {
        if (*cursor == '\n' || *cursor == '\0') {
            size_t len = (size_t)(cursor - line_start);
            if (line_buffer == NULL || len > prev_line_len) {
                char* new_buffer = (char*)realloc(line_buffer, len + 1);
                if (new_buffer == NULL) {
                    free(line_buffer);
                    return SBSV_ERR_ALLOC;
                }
                line_buffer = new_buffer;
                prev_line_len = len;
            }
            sbsv_status status;
            if (line_buffer == NULL) {
                return SBSV_ERR_ALLOC;
            }
            memcpy(line_buffer, line_start, len);
            line_buffer[len] = '\0';

            status = sbsv_parser_parse_line(parser, line_buffer, line_number);
            if (status != SBSV_OK) {
                free(line_buffer);
                return status;
            }

            line_number += 1;
            if (*cursor == '\0') {
                break;
            }
            line_start = cursor + 1;
        }
        cursor += 1;
    }
    if (line_buffer != NULL) {
        free(line_buffer);
    }

    {
        size_t i;
        for (i = 0; i < parser->group_count; ++i) {
            sbsv_group* group = &parser->groups[i];
            if (group->start_index >= 0 && parser->row_count > 0) {
                sbsv_index_range range;
                range.start = (size_t)group->start_index;
                range.end = parser->row_count - 1;
                if (sbsv_group_add_range(group, range) != SBSV_OK) {
                    return SBSV_ERR_ALLOC;
                }
                group->start_index = -1;
            }
        }
    }

    return SBSV_OK;
}

sbsv_status sbsv_parser_load_file(sbsv_parser* parser, FILE* fp) {
    char* line_buf;
    size_t line_len;
    size_t line_cap;
    size_t line_number;
    int ch;

    if (parser == NULL || fp == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    line_buf = NULL;
    line_len = 0;
    line_cap = 0;
    line_number = 1;

    while ((ch = fgetc(fp)) != EOF) {
        if (line_len + 1 >= line_cap) {
            size_t new_cap = (line_cap == 0) ? 128 : (line_cap * 2);
            char* new_buf = (char*)realloc(line_buf, new_cap);
            if (new_buf == NULL) {
                free(line_buf);
                return SBSV_ERR_ALLOC;
            }
            line_buf = new_buf;
            line_cap = new_cap;
        }

        if (ch == '\n') {
            sbsv_status status;
            line_buf[line_len] = '\0';
            status = sbsv_parser_parse_line(parser, line_buf, line_number);
            if (status != SBSV_OK) {
                free(line_buf);
                return status;
            }
            line_len = 0;
            line_number += 1;
            continue;
        }

        line_buf[line_len] = (char)ch;
        line_len += 1;
    }

    if (ferror(fp)) {
        free(line_buf);
        return SBSV_ERR_INVALID_ARG;
    }

    if (line_len > 0 || line_number == 1) {
        sbsv_status status;
        if (line_len + 1 >= line_cap) {
            size_t new_cap = (line_cap == 0) ? 2 : (line_cap + 1);
            char* new_buf = (char*)realloc(line_buf, new_cap);
            if (new_buf == NULL) {
                free(line_buf);
                return SBSV_ERR_ALLOC;
            }
            line_buf = new_buf;
            line_cap = new_cap;
        }
        line_buf[line_len] = '\0';
        status = sbsv_parser_parse_line(parser, line_buf, line_number);
        if (status != SBSV_OK) {
            free(line_buf);
            return status;
        }
    }

    {
        size_t i;
        for (i = 0; i < parser->group_count; ++i) {
            sbsv_group* group = &parser->groups[i];
            if (group->start_index >= 0 && parser->row_count > 0) {
                sbsv_index_range range;
                range.start = (size_t)group->start_index;
                range.end = parser->row_count - 1;
                if (sbsv_group_add_range(group, range) != SBSV_OK) {
                    free(line_buf);
                    return SBSV_ERR_ALLOC;
                }
                group->start_index = -1;
            }
        }
    }

    free(line_buf);
    return SBSV_OK;
}

size_t sbsv_parser_row_count(const sbsv_parser* parser) {
    if (parser == NULL) {
        return 0;
    }
    return parser->row_count;
}

const sbsv_row* sbsv_parser_row_at(const sbsv_parser* parser, size_t index) {
    if (parser == NULL || index >= parser->row_count) {
        return NULL;
    }
    return parser->rows[index];
}

static sbsv_status sbsv_copy_row_refs(sbsv_row* const* rows, size_t count, const sbsv_row*** out_rows) {
    size_t i;
    const sbsv_row** copied = (const sbsv_row**)malloc(sizeof(sbsv_row*) * count);
    if (count > 0 && copied == NULL) {
        return SBSV_ERR_ALLOC;
    }
    for (i = 0; i < count; ++i) {
        copied[i] = rows[i];
    }
    *out_rows = copied;
    return SBSV_OK;
}

sbsv_status sbsv_parser_get_rows_in_order(
    const sbsv_parser* parser,
    const char* const* schemas,
    size_t schema_count,
    const sbsv_row*** out_rows,
    size_t* out_count
) {
    size_t i;

    if (parser == NULL || out_rows == NULL || out_count == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    *out_rows = NULL;
    *out_count = 0;

    if (schemas == NULL || schema_count == 0) {
        *out_count = parser->row_count;
        return sbsv_copy_row_refs(parser->rows, parser->row_count, out_rows);
    }

    {
        const sbsv_schema** selected = (const sbsv_schema**)calloc(schema_count, sizeof(sbsv_schema*));
        size_t* offsets = (size_t*)calloc(schema_count, sizeof(size_t));
        const sbsv_row** result;
        size_t result_count = 0;
        size_t result_capacity = 0;
        sbsv_status status = SBSV_OK;

        if (selected == NULL || offsets == NULL) {
            free(selected);
            free(offsets);
            return SBSV_ERR_ALLOC;
        }

        for (i = 0; i < schema_count; ++i) {
            char* schema_name = NULL;
            status = sbsv_schema_name_from_expr(schemas[i], &schema_name);
            if (status != SBSV_OK) {
                free(selected);
                free(offsets);
                return status;
            }
            selected[i] = sbsv_find_schema_const(parser, schema_name);
            free(schema_name);
            if (selected[i] == NULL) {
                free(selected);
                free(offsets);
                return SBSV_ERR_INVALID_ARG;
            }
        }

        result = NULL;
        while (1) {
            size_t best_idx = (size_t)-1;
            size_t best_id = 0;
            for (i = 0; i < schema_count; ++i) {
                if (offsets[i] >= selected[i]->row_count) {
                    continue;
                }
                if (best_idx == (size_t)-1 || selected[i]->rows[offsets[i]]->id < best_id) {
                    best_idx = i;
                    best_id = selected[i]->rows[offsets[i]]->id;
                }
            }
            if (best_idx == (size_t)-1) {
                break;
            }

            status = sbsv_grow_array((void**)&result, sizeof(sbsv_row*), &result_capacity, result_count + 1);
            if (status != SBSV_OK) {
                free(result);
                free(selected);
                free(offsets);
                return status;
            }
            result[result_count] = selected[best_idx]->rows[offsets[best_idx]];
            result_count += 1;
            offsets[best_idx] += 1;
        }

        free(selected);
        free(offsets);

        *out_rows = result;
        *out_count = result_count;
        return SBSV_OK;
    }
}

sbsv_status sbsv_parser_get_rows_by_index(
    const sbsv_parser* parser,
    const char* schema,
    sbsv_index_range range,
    const sbsv_row*** out_rows,
    size_t* out_count
) {
    const sbsv_schema* found;
    const sbsv_row** result;
    size_t i;
    size_t count;

    if (parser == NULL || schema == NULL || out_rows == NULL || out_count == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    {
        char* schema_name = NULL;
        sbsv_status status = sbsv_schema_name_from_expr(schema, &schema_name);
        if (status != SBSV_OK) {
            return status;
        }
        found = sbsv_find_schema_const(parser, schema_name);
        free(schema_name);
    }
    if (found == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    result = (const sbsv_row**)malloc(sizeof(sbsv_row*) * found->row_count);
    if (found->row_count > 0 && result == NULL) {
        return SBSV_ERR_ALLOC;
    }

    count = 0;
    for (i = 0; i < found->row_count; ++i) {
        size_t id = found->rows[i]->id;
        if (id >= range.start && id <= range.end) {
            result[count] = found->rows[i];
            count += 1;
        }
    }

    *out_rows = result;
    *out_count = count;
    return SBSV_OK;
}

sbsv_status sbsv_parser_get_rows(
    const sbsv_parser* parser,
    const char* schema,
    const sbsv_row*** out_rows,
    size_t* out_count
) {
    const sbsv_schema* found;

    if (parser == NULL || schema == NULL || out_rows == NULL || out_count == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    *out_rows = NULL;
    *out_count = 0;

    {
        char* schema_name = NULL;
        sbsv_status status = sbsv_schema_name_from_expr(schema, &schema_name);
        if (status != SBSV_OK) {
            return status;
        }
        found = sbsv_find_schema_const(parser, schema_name);
        free(schema_name);
    }
    if (found == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    *out_count = found->row_count;
    return sbsv_copy_row_refs(found->rows, found->row_count, out_rows);
}

sbsv_status sbsv_parser_get_group_indices(
    const sbsv_parser* parser,
    const char* group_name,
    sbsv_index_range** out_ranges,
    size_t* out_count
) {
    size_t i;

    if (parser == NULL || group_name == NULL || out_ranges == NULL || out_count == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    for (i = 0; i < parser->group_count; ++i) {
        const sbsv_group* group = &parser->groups[i];
        if (strcmp(group->name, group_name) == 0) {
            sbsv_index_range* copied = (sbsv_index_range*)malloc(sizeof(sbsv_index_range) * group->range_count);
            if (group->range_count > 0 && copied == NULL) {
                return SBSV_ERR_ALLOC;
            }
            if (group->range_count > 0) {
                memcpy(copied, group->ranges, sizeof(sbsv_index_range) * group->range_count);
            }
            *out_ranges = copied;
            *out_count = group->range_count;
            return SBSV_OK;
        }
    }

    return SBSV_ERR_INVALID_ARG;
}

void sbsv_free_row_ref_array(const sbsv_row** rows) {
    free((void*)rows);
}

void sbsv_free_group_indices(sbsv_index_range* ranges) {
    free(ranges);
}

const sbsv_value* sbsv_row_get(const sbsv_row* row, const char* key) {
    size_t i;
    if (row == NULL || key == NULL) {
        return NULL;
    }
    for (i = 0; i < row->field_count; ++i) {
        if (strcmp(row->fields[i].key, key) == 0) {
            return &row->fields[i].value;
        }
    }
    return NULL;
}

const char* sbsv_row_get_string(const sbsv_row* row, const char* key) {
    const sbsv_value* value = sbsv_row_get(row, key);
    if (value == NULL || value->type != SBSV_VALUE_STRING) {
        return NULL;
    }
    return value->data.string_value;
}

long long sbsv_row_get_int(const sbsv_row* row, const char* key, int* valid) {
    const sbsv_value* value;

    value = sbsv_row_get(row, key);
    if (value == NULL || value->type != SBSV_VALUE_INT) {
        if (valid != NULL) {
            *valid = 0;
        }
        return 0;
    }

    if (valid != NULL) {
        *valid = 1;
    }
    return value->data.int_value;
}

double sbsv_row_get_float(const sbsv_row* row, const char* key, int* valid) {
    const sbsv_value* value;

    value = sbsv_row_get(row, key);
    if (value == NULL || value->type != SBSV_VALUE_FLOAT) {
        if (valid != NULL) {
            *valid = 0;
        }
        return 0.0;
    }

    if (valid != NULL) {
        *valid = 1;
    }
    return value->data.float_value;
}

int sbsv_row_get_bool(const sbsv_row* row, const char* key, int* valid) {
    const sbsv_value* value;

    value = sbsv_row_get(row, key);
    if (value == NULL || value->type != SBSV_VALUE_BOOL) {
        if (valid != NULL) {
            *valid = 0;
        }
        return 0;
    }

    if (valid != NULL) {
        *valid = 1;
    }
    return value->data.bool_value;
}

const sbsv_value_list* sbsv_row_get_list(const sbsv_row* row, const char* key) {
    const sbsv_value* value = sbsv_row_get(row, key);
    if (value == NULL || value->type != SBSV_VALUE_LIST) {
        return NULL;
    }
    return &value->data.list;
}

void* sbsv_row_get_custom_ptr(const sbsv_row* row, const char* key) {
    const sbsv_value* value = sbsv_row_get(row, key);
    if (value == NULL || value->type != SBSV_VALUE_CUSTOM) {
        return NULL;
    }
    return value->data.custom_ptr;
}