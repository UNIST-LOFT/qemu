#include "sbsv.h"

#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct sbsv_schema_field {
    char* name_with_tag;
    char* name;
    char* type_name;
    int nullable;
};

struct sbsv_schema {
    char* name;
    sbsv_schema_field* fields;
    size_t field_count;
    size_t field_capacity;
    sbsv_row** rows;
    size_t row_count;
    size_t row_capacity;
};

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

typedef struct {
    char* literal;
    sbsv_schema_field capture;
    int is_capture;
} sbsv_ignore_prefix_token;

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

    sbsv_ignore_prefix_token* ignored_prefix;
    size_t ignored_prefix_count;
    size_t ignored_prefix_capacity;
    int save_ignored_prefix;

    sbsv_row** rows;
    size_t row_count;
    size_t row_capacity;
};

struct sbsv_body_parser {
    char* last_error;
    sbsv_schema schema;
    int has_schema;
    sbsv_custom_type* custom_types;
    size_t custom_type_count;
    size_t custom_type_capacity;
};

typedef struct {
    char* schema_name;
    char** data_tokens;
    size_t data_count;
    size_t data_capacity;
    sbsv_field* ignored_fields;
    size_t ignored_field_count;
    size_t ignored_field_capacity;
} sbsv_preprocessed_line;

static sbsv_status sbsv_parse_row_for_schema(
    sbsv_parser* parser,
    sbsv_schema* schema,
    char** tokens,
    size_t token_count,
    sbsv_row** out_row
);

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

static void sbsv_body_parser_set_error(sbsv_body_parser* parser, const char* format, ...) {
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

static int sbsv_validate_name_range(const char* name, size_t len) {
    size_t i;

    if (name == NULL || len == 0) {
        return 0;
    }
    for (i = 0; i < len; ++i) {
        unsigned char ch = (unsigned char)name[i];
        if (!(isalnum(ch) || ch == '_' || ch == '-')) {
            return 0;
        }
    }
    return 1;
}

static int sbsv_validate_name(const char* name) {
    if (name == NULL) {
        return 0;
    }
    return sbsv_validate_name_range(name, strlen(name));
}

static int sbsv_validate_tagged_field_name(const char* name) {
    const char* start;
    const char* cursor;

    if (name == NULL || name[0] == '\0') {
        return 0;
    }

    start = name;
    cursor = name;
    while (1) {
        if (*cursor == '$' || *cursor == '\0') {
            size_t len = (size_t)(cursor - start);
            if (!sbsv_validate_name_range(start, len)) {
                return 0;
            }
            if (*cursor == '\0') {
                return 1;
            }
            start = cursor + 1;
        }
        cursor += 1;
    }
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
        if (new_capacity > SIZE_MAX / 2) {
            return SBSV_ERR_ALLOC;
        }
        new_capacity *= 2;
    }

    if (elem_size != 0 && new_capacity > SIZE_MAX / elem_size) {
        return SBSV_ERR_ALLOC;
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

void sbsv_row_free(sbsv_row* row) {
    size_t i;

    if (row == NULL) {
        return;
    }

    for (i = 0; i < row->field_count; ++i) {
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

static void sbsv_ignore_prefix_token_free(sbsv_ignore_prefix_token* token) {
    if (token == NULL) {
        return;
    }
    free(token->literal);
    if (token->is_capture) {
        sbsv_schema_field_free(&token->capture);
    }
    memset(token, 0, sizeof(*token));
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

    for (i = 0; i < parser->ignored_prefix_count; ++i) {
        sbsv_ignore_prefix_token_free(&parser->ignored_prefix[i]);
    }
    free(parser->ignored_prefix);

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

static sbsv_custom_type* sbsv_find_custom_type_in_array(sbsv_custom_type* custom_types, size_t custom_type_count, const char* type_name) {
    size_t i;
    for (i = 0; i < custom_type_count; ++i) {
        if (strcmp(custom_types[i].name, type_name) == 0) {
            return &custom_types[i];
        }
    }
    return NULL;
}

static int sbsv_type_is_supported(sbsv_custom_type* custom_types, size_t custom_type_count, const char* type_name) {
    size_t len;
    char* subtype;
    int supported;

    if (type_name == NULL || type_name[0] == '\0') {
        return 0;
    }
    if (strcmp(type_name, "int") == 0 || strcmp(type_name, "float") == 0 ||
        strcmp(type_name, "str") == 0 || strcmp(type_name, "bool") == 0 ||
        strcmp(type_name, "null") == 0) {
        return 1;
    }
    len = strlen(type_name);
    if (strncmp(type_name, "list", 4) == 0) {
        if (len < 7 || strncmp(type_name, "list[", 5) != 0 || type_name[len - 1] != ']') {
            return 0;
        }
        subtype = (char*)malloc(len - 5);
        if (subtype == NULL) {
            return 0;
        }
        memcpy(subtype, type_name + 5, len - 6);
        subtype[len - 6] = '\0';
        supported = sbsv_type_is_supported(custom_types, custom_type_count, subtype);
        free(subtype);
        return supported;
    }
    return sbsv_find_custom_type_in_array(custom_types, custom_type_count, type_name) != NULL;
}

static int sbsv_schema_names_conflict(const char* left, const char* right) {
    const char* l = left;
    const char* r = right;

    while (1) {
        const char* lend = strchr(l, '$');
        const char* rend = strchr(r, '$');
        size_t llen = (lend == NULL) ? strlen(l) : (size_t)(lend - l);
        size_t rlen = (rend == NULL) ? strlen(r) : (size_t)(rend - r);

        if (llen != rlen || strncmp(l, r, llen) != 0) {
            return 0;
        }
        if (lend == NULL || rend == NULL) {
            return 1;
        }
        l = lend + 1;
        r = rend + 1;
    }
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
    {
        char* unescaped_key = NULL;
        if (sbsv_unescape_str(*out_key, &unescaped_key) != SBSV_OK) {
            free(*out_key);
            *out_key = NULL;
            return;
        }
        free(*out_key);
        *out_key = unescaped_key;
    }

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
            {
                char* unescaped_key = NULL;
                if (sbsv_unescape_str(*out_key, &unescaped_key) != SBSV_OK) {
                    free(*out_key);
                    *out_key = NULL;
                } else {
                    free(*out_key);
                    *out_key = unescaped_key;
                }
            }
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
    {
        char* unescaped_key = NULL;
        if (sbsv_unescape_str(*out_key, &unescaped_key) != SBSV_OK) {
            free(*out_key);
            *out_key = NULL;
            return;
        }
        free(*out_key);
        *out_key = unescaped_key;
    }

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
    int body_started = 0;

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
    if (!sbsv_validate_name(parsed.name)) {
        sbsv_parser_set_error(parser, "Invalid schema name '%s': use only [A-Za-z0-9_-]", parsed.name);
        sbsv_schema_free(&parsed);
        sbsv_free_token_list(&tokens);
        return SBSV_ERR_INVALID_ARG;
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

        if (strchr(tokens.items[i], ':') == NULL) {
            if (body_started || strlen(value) != 0) {
                sbsv_parser_set_error(parser, "Invalid schema token [%s]: missing type annotation", tokens.items[i]);
                free(key);
                free(value);
                sbsv_schema_free(&parsed);
                sbsv_free_token_list(&tokens);
                return SBSV_ERR_INVALID_ARG;
            }
            if (!sbsv_validate_name(key)) {
                sbsv_parser_set_error(parser, "Invalid sub-schema name '%s': use only [A-Za-z0-9_-]", key);
                free(key);
                free(value);
                sbsv_schema_free(&parsed);
                sbsv_free_token_list(&tokens);
                return SBSV_ERR_INVALID_ARG;
            }
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
        body_started = 1;

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
        if (!sbsv_validate_tagged_field_name(key)) {
            sbsv_parser_set_error(parser, "Invalid schema field name '%s': use only [A-Za-z0-9_-] and optional $ tags", key);
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
        }
        if (!sbsv_type_is_supported(parser->custom_types, parser->custom_type_count, value)) {
            sbsv_parser_set_error(parser, "Unsupported type: %s", value);
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
        }
        if (parsed.field_count == 0 && field.nullable) {
            sbsv_parser_set_error(parser, "Invalid schema %s: first body field '%s' cannot be nullable", schema_expr, key);
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
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

    for (i = 0; i < parser->schema_count; ++i) {
        if (sbsv_schema_names_conflict(parsed.name, parser->schemas[i].name)) {
            sbsv_parser_set_error(parser, "Schema '%s' conflicts with existing schema '%s'", parsed.name, parser->schemas[i].name);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
        }
    }

    status = sbsv_grow_array((void**)&parser->schemas, sizeof(sbsv_schema), &parser->schema_capacity, parser->schema_count + 1);
    if (status != SBSV_OK) {
        sbsv_schema_free(&parsed);
        sbsv_free_token_list(&tokens);
        return status;
    }

    parser->schemas[parser->schema_count] = parsed;
    parser->schema_count += 1;

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
    if (parser->schema_count > 0) {
        sbsv_parser_set_error(parser, "add_custom_type() must be called before add_schema()");
        return SBSV_ERR_INVALID_ARG;
    }
    if (!sbsv_validate_name(type_name)) {
        sbsv_parser_set_error(parser, "Invalid custom type name '%s': use only [A-Za-z0-9_-]", type_name);
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

sbsv_status sbsv_parser_ignore_prefix(
    sbsv_parser* parser,
    const char* prefix,
    int save_ignored
) {
    sbsv_token_list tokens;
    sbsv_ignore_prefix_token* parsed_tokens = NULL;
    size_t parsed_count = 0;
    size_t parsed_capacity = 0;
    size_t i;
    sbsv_status status;

    if (parser == NULL || prefix == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }
    if (parser->schema_count > 0) {
        sbsv_parser_set_error(parser, "ignore_prefix() must be called before add_schema()");
        return SBSV_ERR_INVALID_ARG;
    }

    memset(&tokens, 0, sizeof(tokens));
    status = sbsv_tokenize_line(prefix, &tokens);
    if (status != SBSV_OK || tokens.count == 0) {
        sbsv_parser_set_error(parser, "Invalid ignore prefix %s: too short", prefix);
        sbsv_free_token_list(&tokens);
        return status == SBSV_OK ? SBSV_ERR_INVALID_ARG : status;
    }

    for (i = 0; i < tokens.count; ++i) {
        char* key = NULL;
        char* value = NULL;
        sbsv_ignore_prefix_token token;

        memset(&token, 0, sizeof(token));
        sbsv_split_token_schema(tokens.items[i], &key, &value);
        if (key == NULL || value == NULL) {
            free(key);
            free(value);
            status = SBSV_ERR_ALLOC;
            goto fail;
        }
        if (key[0] == '\0') {
            sbsv_parser_set_error(parser, "Invalid ignore prefix token [%s]: empty name", tokens.items[i]);
            free(key);
            free(value);
            status = SBSV_ERR_INVALID_ARG;
            goto fail;
        }

        if (key[0] != '$') {
            token.literal = sbsv_strdup_local(tokens.items[i]);
            free(key);
            free(value);
            if (token.literal == NULL) {
                status = SBSV_ERR_ALLOC;
                goto fail;
            }
        } else {
            const char* capture_name = key + 1;
            if (!sbsv_validate_name(capture_name)) {
                sbsv_parser_set_error(parser, "Invalid ignored prefix name '%s': use only [A-Za-z0-9_-]", capture_name);
                free(key);
                free(value);
                status = SBSV_ERR_INVALID_ARG;
                goto fail;
            }
            if (value[0] == '\0') {
                free(value);
                value = sbsv_strdup_local("str");
                if (value == NULL) {
                    free(key);
                    status = SBSV_ERR_ALLOC;
                    goto fail;
                }
            }
            if (!sbsv_type_is_supported(parser->custom_types, parser->custom_type_count, value)) {
                sbsv_parser_set_error(parser, "Unsupported type: %s", value);
                free(key);
                free(value);
                status = SBSV_ERR_INVALID_ARG;
                goto fail;
            }

            token.is_capture = 1;
            token.capture.name_with_tag = sbsv_strdup_local(key);
            token.capture.name = sbsv_strdup_local(key);
            token.capture.type_name = sbsv_strdup_local(value);
            token.capture.nullable = 0;
            free(key);
            free(value);
            if (token.capture.name_with_tag == NULL || token.capture.name == NULL || token.capture.type_name == NULL) {
                sbsv_ignore_prefix_token_free(&token);
                status = SBSV_ERR_ALLOC;
                goto fail;
            }
        }

        status = sbsv_grow_array((void**)&parsed_tokens, sizeof(sbsv_ignore_prefix_token), &parsed_capacity, parsed_count + 1);
        if (status != SBSV_OK) {
            sbsv_ignore_prefix_token_free(&token);
            goto fail;
        }
        parsed_tokens[parsed_count] = token;
        parsed_count += 1;
    }

    for (i = 0; i < parser->ignored_prefix_count; ++i) {
        sbsv_ignore_prefix_token_free(&parser->ignored_prefix[i]);
    }
    free(parser->ignored_prefix);
    parser->ignored_prefix = parsed_tokens;
    parser->ignored_prefix_count = parsed_count;
    parser->ignored_prefix_capacity = parsed_capacity;
    parser->save_ignored_prefix = save_ignored ? 1 : 0;
    sbsv_free_token_list(&tokens);
    return SBSV_OK;

fail:
    for (i = 0; i < parsed_count; ++i) {
        sbsv_ignore_prefix_token_free(&parsed_tokens[i]);
    }
    free(parsed_tokens);
    sbsv_free_token_list(&tokens);
    return status;
}

sbsv_body_parser* sbsv_body_parser_new(void) {
    return (sbsv_body_parser*)calloc(1, sizeof(sbsv_body_parser));
}

void sbsv_body_parser_free(sbsv_body_parser* parser) {
    size_t i;

    if (parser == NULL) {
        return;
    }

    sbsv_schema_free(&parser->schema);
    for (i = 0; i < parser->custom_type_count; ++i) {
        free(parser->custom_types[i].name);
    }
    free(parser->custom_types);
    free(parser->last_error);
    free(parser);
}

const char* sbsv_body_parser_last_error(const sbsv_body_parser* parser) {
    if (parser == NULL) {
        return "invalid parser";
    }
    return parser->last_error;
}

sbsv_status sbsv_body_parser_add_custom_type(
    sbsv_body_parser* parser,
    const char* type_name,
    sbsv_custom_type_fn converter,
    void* user_data
) {
    sbsv_custom_type* existing;
    sbsv_status status;

    if (parser == NULL || type_name == NULL || converter == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }
    if (parser->has_schema) {
        sbsv_body_parser_set_error(parser, "add_custom_type() must be called before set_schema()");
        return SBSV_ERR_INVALID_ARG;
    }
    if (!sbsv_validate_name(type_name)) {
        sbsv_body_parser_set_error(parser, "Invalid custom type name '%s': use only [A-Za-z0-9_-]", type_name);
        return SBSV_ERR_INVALID_ARG;
    }

    existing = sbsv_find_custom_type_in_array(parser->custom_types, parser->custom_type_count, type_name);
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

sbsv_status sbsv_body_parser_set_schema(sbsv_body_parser* parser, const char* schema_body) {
    sbsv_token_list tokens;
    sbsv_schema parsed;
    size_t i;
    sbsv_status status;

    if (parser == NULL || schema_body == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    memset(&tokens, 0, sizeof(tokens));
    memset(&parsed, 0, sizeof(parsed));
    parsed.name = sbsv_strdup_local("");
    if (parsed.name == NULL) {
        return SBSV_ERR_ALLOC;
    }

    status = sbsv_tokenize_line(schema_body, &tokens);
    if (status != SBSV_OK) {
        sbsv_schema_free(&parsed);
        sbsv_body_parser_set_error(parser, "Invalid schema body: failed to tokenize");
        return status;
    }

    for (i = 0; i < tokens.count; ++i) {
        char* key = NULL;
        char* value = NULL;
        sbsv_schema_field field;

        memset(&field, 0, sizeof(field));
        if (strchr(tokens.items[i], ':') == NULL) {
            sbsv_body_parser_set_error(parser, "Invalid schema token [%s]: missing type annotation", tokens.items[i]);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
        }

        sbsv_split_token_schema(tokens.items[i], &key, &value);
        if (key == NULL || value == NULL) {
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_ALLOC;
        }
        if (strlen(key) > 0 && key[strlen(key) - 1] == '?') {
            key[strlen(key) - 1] = '\0';
            field.nullable = 1;
        }
        if (!sbsv_validate_tagged_field_name(key)) {
            sbsv_body_parser_set_error(parser, "Invalid schema field name '%s': use only [A-Za-z0-9_-] and optional $ tags", key);
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
        }
        if (!sbsv_type_is_supported(parser->custom_types, parser->custom_type_count, value)) {
            sbsv_body_parser_set_error(parser, "Unsupported type: %s", value);
            free(key);
            free(value);
            sbsv_schema_free(&parsed);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
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

    sbsv_schema_free(&parser->schema);
    parser->schema = parsed;
    parser->has_schema = 1;
    sbsv_free_token_list(&tokens);
    return SBSV_OK;
}

sbsv_status sbsv_body_parser_parse(
    sbsv_body_parser* parser,
    const char* body,
    sbsv_row** out_row
) {
    sbsv_token_list tokens;
    sbsv_parser fake_parser;
    sbsv_row* row = NULL;
    sbsv_status status;

    if (parser == NULL || body == NULL || out_row == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }
    *out_row = NULL;
    if (!parser->has_schema) {
        sbsv_body_parser_set_error(parser, "schema body is not set");
        return SBSV_ERR_INVALID_ARG;
    }

    memset(&tokens, 0, sizeof(tokens));
    status = sbsv_tokenize_line(body, &tokens);
    if (status != SBSV_OK) {
        sbsv_body_parser_set_error(parser, "Invalid body: failed to tokenize");
        return status;
    }

    memset(&fake_parser, 0, sizeof(fake_parser));
    fake_parser.ignore_unknown = 1;
    fake_parser.custom_types = parser->custom_types;
    fake_parser.custom_type_count = parser->custom_type_count;
    status = sbsv_parse_row_for_schema(&fake_parser, &parser->schema, tokens.items, tokens.count, &row);
    if (status != SBSV_OK) {
        const char* detail = fake_parser.last_error ? fake_parser.last_error : "parse error";
        sbsv_body_parser_set_error(parser, "%s", detail);
        free(fake_parser.last_error);
        sbsv_free_token_list(&tokens);
        return status;
    }
    free(fake_parser.last_error);
    sbsv_free_token_list(&tokens);
    row->id = (size_t)-1;
    row->schema_name = parser->schema.name;
    *out_row = row;
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
            sbsv_value_clear(out_value);
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
    char* decoded = NULL;
    const char* value = raw;

    if (strncmp(type_name, "list[", 5) == 0) {
        return sbsv_parse_list_value(parser, type_name, raw, out_value);
    }

    if (sbsv_unescape_str(raw, &decoded) != SBSV_OK) {
        sbsv_parser_set_error(parser, "Invalid string value: %s", raw);
        return SBSV_ERR_INVALID_ARG;
    }
    value = decoded;

    if (strcmp(type_name, "int") == 0) {
        long long parsed;
        errno = 0;
        parsed = strtoll(value, &end_ptr, 10);
        if (errno != 0 || *end_ptr != '\0') {
            sbsv_parser_set_error(parser, "Invalid int value: %s", value);
            free(decoded);
            return SBSV_ERR_INVALID_ARG;
        }
        out_value->type = SBSV_VALUE_INT;
        out_value->data.int_value = parsed;
        free(decoded);
        return SBSV_OK;
    }

    if (strcmp(type_name, "float") == 0) {
        double parsed;
        errno = 0;
        parsed = strtod(value, &end_ptr);
        if (errno != 0 || *end_ptr != '\0') {
            sbsv_parser_set_error(parser, "Invalid float value: %s", value);
            free(decoded);
            return SBSV_ERR_INVALID_ARG;
        }
        out_value->type = SBSV_VALUE_FLOAT;
        out_value->data.float_value = parsed;
        free(decoded);
        return SBSV_OK;
    }

    if (strcmp(type_name, "str") == 0) {
        sbsv_status status = sbsv_value_set_string(out_value, value);
        free(decoded);
        return status;
    }

    if (strcmp(type_name, "bool") == 0) {
        int bool_value;
        if (!sbsv_parse_bool(value, &bool_value)) {
            sbsv_parser_set_error(parser, "Invalid boolean value: %s", value);
            free(decoded);
            return SBSV_ERR_INVALID_ARG;
        }
        out_value->type = SBSV_VALUE_BOOL;
        out_value->data.bool_value = bool_value;
        free(decoded);
        return SBSV_OK;
    }

    if (strcmp(type_name, "null") == 0) {
        char lowered[8];
        size_t len = strlen(value);
        size_t i;
        if (len >= sizeof(lowered)) {
            sbsv_parser_set_error(parser, "Invalid null value: %s", value);
            free(decoded);
            return SBSV_ERR_INVALID_ARG;
        }
        for (i = 0; i < len; ++i) {
            lowered[i] = (char)tolower((unsigned char)value[i]);
        }
        lowered[len] = '\0';
        if (strcmp(lowered, "null") != 0) {
            sbsv_parser_set_error(parser, "Invalid null value: %s", value);
            free(decoded);
            return SBSV_ERR_INVALID_ARG;
        }
        out_value->type = SBSV_VALUE_NULL;
        free(decoded);
        return SBSV_OK;
    }

    custom = sbsv_find_custom_type(parser, type_name);
    if (custom != NULL) {
        sbsv_status status = custom->converter(value, out_value, custom->user_data);
        free(decoded);
        return status;
    }

    sbsv_parser_set_error(parser, "Unsupported type: %s", type_name);
    free(decoded);
    return SBSV_ERR_INVALID_ARG;
}

static sbsv_status sbsv_preprocess_line(sbsv_parser* parser, const char* line, sbsv_preprocessed_line* out_line) {
    sbsv_token_list tokens;
    size_t i;
    size_t start_index = 0;
    int may_have_sub_schema = 1;
    sbsv_status status;

    memset(out_line, 0, sizeof(*out_line));
    memset(&tokens, 0, sizeof(tokens));

    status = sbsv_tokenize_line(line, &tokens);
    if (status != SBSV_OK) {
        return status;
    }

    if (parser != NULL && parser->ignored_prefix_count > 0) {
        if (tokens.count < parser->ignored_prefix_count) {
            sbsv_parser_set_error(parser, "Invalid data: expected at least %zu ignored prefix fields, got %zu", parser->ignored_prefix_count, tokens.count);
            sbsv_free_token_list(&tokens);
            return SBSV_ERR_INVALID_ARG;
        }

        for (i = 0; i < parser->ignored_prefix_count; ++i) {
            sbsv_ignore_prefix_token* prefix_token = &parser->ignored_prefix[i];
            if (!prefix_token->is_capture) {
                if (strcmp(tokens.items[i], prefix_token->literal) != 0) {
                    sbsv_parser_set_error(parser, "Invalid ignored prefix token [%s]: expected [%s]", tokens.items[i], prefix_token->literal);
                    sbsv_free_token_list(&tokens);
                    return SBSV_ERR_INVALID_ARG;
                }
                continue;
            }

            if (parser->save_ignored_prefix) {
                sbsv_field saved;
                memset(&saved, 0, sizeof(saved));
                saved.name_with_tag = prefix_token->capture.name_with_tag;
                saved.name = prefix_token->capture.name;
                sbsv_value_init(&saved.value);
                status = sbsv_parse_value(parser, prefix_token->capture.type_name, tokens.items[i], &saved.value);
                if (status != SBSV_OK) {
                    sbsv_value_clear(&saved.value);
                    sbsv_free_token_list(&tokens);
                    return status;
                }
                status = sbsv_grow_array((void**)&out_line->ignored_fields, sizeof(sbsv_field), &out_line->ignored_field_capacity, out_line->ignored_field_count + 1);
                if (status != SBSV_OK) {
                    sbsv_value_clear(&saved.value);
                    sbsv_free_token_list(&tokens);
                    return status;
                }
                out_line->ignored_fields[out_line->ignored_field_count] = saved;
                out_line->ignored_field_count += 1;
            }
        }
        start_index = parser->ignored_prefix_count;
    }

    for (i = start_index; i < tokens.count; ++i) {
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
    for (i = 0; i < pre->ignored_field_count; ++i) {
        sbsv_value_clear(&pre->ignored_fields[i].value);
    }
    free(pre->ignored_fields);
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
        sbsv_parser_set_error(parser, "Invalid data: expected at least %zu fields, got %zu", schema->field_count, token_count);
        return SBSV_ERR_INVALID_ARG;
    }

    row = (sbsv_row*)calloc(1, sizeof(sbsv_row));
    if (row == NULL) {
        return SBSV_ERR_ALLOC;
    }
    row->schema_name = schema->name;
    row->field_count = schema->field_count;
    row->fields = (sbsv_field*)calloc(schema->field_count, sizeof(sbsv_field));
    if (row->fields == NULL) {
        free(row);
        return SBSV_ERR_ALLOC;
    }

    for (field_index = 0; field_index < schema->field_count; ++field_index) {
        sbsv_schema_field* field = &schema->fields[field_index];
        int matched = 0;

        row->fields[field_index].name_with_tag = field->name_with_tag;
        row->fields[field_index].name = field->name;
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
                sbsv_parser_set_error(parser, "Invalid data token [%s]: empty value for non-nullable key '%s'", tokens[queue_index - 1], field->name);
                sbsv_row_free(row);
                return SBSV_ERR_INVALID_ARG;
            }

            convert_status = sbsv_parse_value(parser, field->type_name, value, &row->fields[field_index].value);
            if (convert_status != SBSV_OK) {
                const char* detail = parser->last_error ? parser->last_error : "conversion failed";
                char* detail_copy = sbsv_strdup_local(detail);
                if (detail_copy != NULL) {
                    sbsv_parser_set_error(
                        parser,
                        "Invalid value for key '%s' as type '%s': '%s' (%s)",
                        field->name,
                        field->type_name,
                        value,
                        detail_copy
                    );
                    free(detail_copy);
                }
                free(key);
                free(value);
                sbsv_row_free(row);
                return convert_status;
            }
            free(key);
            free(value);
            matched = 1;
            break;
        }

        if (!matched) {
            sbsv_parser_set_error(parser, "Invalid data: missing key '%s'", field->name);
            sbsv_row_free(row);
            return SBSV_ERR_INVALID_ARG;
        }
    }

    *out_row = row;
    return SBSV_OK;
}

static sbsv_status sbsv_row_prepend_fields(sbsv_row* row, sbsv_preprocessed_line* pre) {
    sbsv_field* merged;

    if (row == NULL || pre == NULL || pre->ignored_field_count == 0) {
        return SBSV_OK;
    }

    merged = (sbsv_field*)calloc(row->field_count + pre->ignored_field_count, sizeof(sbsv_field));
    if (merged == NULL) {
        return SBSV_ERR_ALLOC;
    }

    memcpy(merged, pre->ignored_fields, sizeof(sbsv_field) * pre->ignored_field_count);
    memcpy(merged + pre->ignored_field_count, row->fields, sizeof(sbsv_field) * row->field_count);
    free(row->fields);
    row->fields = merged;
    row->field_count += pre->ignored_field_count;
    free(pre->ignored_fields);
    pre->ignored_fields = NULL;
    pre->ignored_field_count = 0;
    pre->ignored_field_capacity = 0;
    return SBSV_OK;
}

static sbsv_status sbsv_parser_parse_line_internal(sbsv_parser* parser, const char* line, size_t line_number, int append, sbsv_row** out_row) {
    char* stripped;
    sbsv_preprocessed_line pre;
    sbsv_schema* schema;
    sbsv_row* row = NULL;
    sbsv_status status;

    if (out_row != NULL) {
        *out_row = NULL;
    }

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

    status = sbsv_preprocess_line(parser, stripped, &pre);
    if (status != SBSV_OK) {
        const char* detail = parser->last_error ? parser->last_error : "parse error";
        char* detail_copy = sbsv_strdup_local(detail);
        if (detail_copy != NULL) {
            sbsv_parser_set_error(parser, "Parse error (line=%zu, input='%s'): %s", line_number, stripped, detail_copy);
            free(detail_copy);
        }
        sbsv_preprocessed_line_free(&pre);
        free(stripped);
        return status;
    }

    if (pre.schema_name == NULL) {
        if (parser->ignore_unknown) {
            sbsv_preprocessed_line_free(&pre);
            free(stripped);
            return SBSV_OK;
        }
        sbsv_parser_set_error(parser, "Parse error (line=%zu, schema=<missing>, input='%s'): Unknown schema '<missing>'", line_number, stripped);
        sbsv_preprocessed_line_free(&pre);
        free(stripped);
        return SBSV_ERR_INVALID_ARG;
    }

    schema = sbsv_find_schema(parser, pre.schema_name);
    if (schema == NULL) {
        if (parser->ignore_unknown) {
            sbsv_preprocessed_line_free(&pre);
            free(stripped);
            return SBSV_OK;
        }
        sbsv_parser_set_error(parser, "Parse error (line=%zu, schema=%s, input='%s'): Unknown schema '%s'", line_number, pre.schema_name, stripped, pre.schema_name);
        sbsv_preprocessed_line_free(&pre);
        free(stripped);
        return SBSV_ERR_INVALID_ARG;
    }

    status = sbsv_parse_row_for_schema(parser, schema, pre.data_tokens, pre.data_count, &row);
    if (status != SBSV_OK) {
        const char* detail = parser->last_error ? parser->last_error : "parse error";
        char* detail_copy = sbsv_strdup_local(detail);
        if (detail_copy != NULL) {
            sbsv_parser_set_error(parser, "Parse error (line=%zu, schema=%s, input='%s'): %s", line_number, schema->name, stripped, detail_copy);
            free(detail_copy);
        } else {
            sbsv_parser_set_error(parser, "Parse error (line=%zu, schema=%s, input='%s'): parse error", line_number, schema->name, stripped);
        }
        sbsv_preprocessed_line_free(&pre);
        free(stripped);
        return status;
    }

    status = sbsv_row_prepend_fields(row, &pre);
    if (status != SBSV_OK) {
        sbsv_row_free(row);
        sbsv_preprocessed_line_free(&pre);
        free(stripped);
        return status;
    }

    if (append) {
        status = sbsv_parser_append_row(parser, schema, row);
        if (status != SBSV_OK) {
            sbsv_row_free(row);
        }
    } else {
        row->id = (size_t)-1;
        row->schema_name = schema->name;
        if (out_row != NULL) {
            *out_row = row;
        }
    }

    sbsv_preprocessed_line_free(&pre);
    free(stripped);
    return status;
}

sbsv_status sbsv_parser_parse_line(sbsv_parser* parser, const char* line, size_t line_number) {
    return sbsv_parser_parse_line_internal(parser, line, line_number, 1, NULL);
}

sbsv_status sbsv_parser_parse_line_detached(
    sbsv_parser* parser,
    const char* line,
    size_t line_number,
    sbsv_row** out_row
) {
    if (out_row == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }
    return sbsv_parser_parse_line_internal(parser, line, line_number, 0, out_row);
}

sbsv_status sbsv_parser_finish(sbsv_parser* parser) {
    size_t i;

    if (parser == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

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
    return SBSV_OK;
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

    return sbsv_parser_finish(parser);
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

    free(line_buf);
    return sbsv_parser_finish(parser);
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
        if ((row->fields[i].name_with_tag != NULL && strcmp(row->fields[i].name_with_tag, key) == 0) ||
            (row->fields[i].name != NULL && strcmp(row->fields[i].name, key) == 0)) {
            return &row->fields[i].value;
        }
    }
    return NULL;
}

const char* sbsv_field_name(const sbsv_field* field) {
    if (field == NULL) {
        return NULL;
    }
    return field->name;
}

const char* sbsv_field_name_with_tag(const sbsv_field* field) {
    if (field == NULL) {
        return NULL;
    }
    return field->name_with_tag;
}

const char* sbsv_row_schema_name(const sbsv_row* row) {
    if (row == NULL) {
        return NULL;
    }
    return row->schema_name;
}

size_t sbsv_row_field_count(const sbsv_row* row) {
    if (row == NULL) {
        return 0;
    }
    return row->field_count;
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
