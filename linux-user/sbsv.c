#include "sbsv.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static bool sbsv_is_space(char ch);

static const char* sbsv_escape_replacement(char ch, size_t* out_len) {
    switch (ch) {
        case '\b':
            *out_len = 2;
            return "\\b";
        case '\t':
            *out_len = 2;
            return "\\t";
        case '\n':
            *out_len = 2;
            return "\\n";
        case '\f':
            *out_len = 2;
            return "\\f";
        case '\r':
            *out_len = 2;
            return "\\r";
        case '\"':
            *out_len = 2;
            return "\\\"";
        case '\\':
            *out_len = 2;
            return "\\\\";
        case '[':
            *out_len = 2;
            return "\\[";
        case ']':
            *out_len = 2;
            return "\\]";
        default:
            *out_len = 0;
            return NULL;
    }
}

static bool sbsv_unescape_char(char escaped, char* out_raw) {
    switch (escaped) {
        case 'b':
            *out_raw = '\b';
            return true;
        case 't':
            *out_raw = '\t';
            return true;
        case 'n':
            *out_raw = '\n';
            return true;
        case 'f':
            *out_raw = '\f';
            return true;
        case 'r':
            *out_raw = '\r';
            return true;
        case '"':
            *out_raw = '"';
            return true;
        case '\\':
            *out_raw = '\\';
            return true;
        case '[':
            *out_raw = '[';
            return true;
        case ']':
            *out_raw = ']';
            return true;
        default:
            return false;
    }
}

static bool sbsv_can_start_quote(const char* current, size_t current_len) {
    size_t start = 0;
    size_t end = current_len;
    size_t words = 0;
    bool in_word = false;

    while (start < end && sbsv_is_space(current[start])) {
        start += 1;
    }
    while (end > start && sbsv_is_space(current[end - 1])) {
        end -= 1;
    }
    if (start == end) {
        return true;
    }
    if (current_len == 0 || !sbsv_is_space(current[current_len - 1])) {
        return false;
    }
    while (start < end) {
        if (sbsv_is_space(current[start])) {
            in_word = false;
        } else if (!in_word) {
            words += 1;
            in_word = true;
        }
        start += 1;
    }
    return words == 1;
}

const char* sbsv_status_str(sbsv_status status) {
    switch (status) {
        case SBSV_OK:
            return "ok";
        case SBSV_ERR_INVALID_ARG:
            return "invalid argument";
        case SBSV_ERR_ALLOC:
            return "allocation failed";
        default:
            return "unknown status";
    }
}

static bool sbsv_is_space(char ch) {
    return ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' || ch == '\f' || ch == '\v';
}

static void sbsv_trim_view(const char** start, const char** end) {
    while (*start < *end && sbsv_is_space(**start)) {
        *start += 1;
    }

    while (*end > *start && sbsv_is_space(*(*end - 1))) {
        *end -= 1;
    }
}

static sbsv_status sbsv_append_char(char** buffer, size_t* len, size_t* cap, char ch) {
    char* new_buffer;

    if (*len + 1 >= *cap) {
        size_t new_cap = (*cap == 0) ? 16 : (*cap * 2);
        while (*len + 1 >= new_cap) {
            new_cap *= 2;
        }
        new_buffer = (char*)realloc(*buffer, new_cap);
        if (new_buffer == NULL) {
            return SBSV_ERR_ALLOC;
        }
        *buffer = new_buffer;
        *cap = new_cap;
    }

    (*buffer)[*len] = ch;
    *len += 1;
    (*buffer)[*len] = '\0';
    return SBSV_OK;
}

static sbsv_status sbsv_append_bytes(char** buffer, size_t* len, size_t* cap, const char* src, size_t src_len) {
    char* new_buffer;

    if (*len + src_len >= *cap) {
        size_t new_cap = (*cap == 0) ? 16 : (*cap * 2);
        while (*len + src_len >= new_cap) {
            new_cap *= 2;
        }
        new_buffer = (char*)realloc(*buffer, new_cap);
        if (new_buffer == NULL) {
            return SBSV_ERR_ALLOC;
        }
        *buffer = new_buffer;
        *cap = new_cap;
    }

    if (src_len > 0) {
        memcpy(*buffer + *len, src, src_len);
    }
    *len += src_len;
    (*buffer)[*len] = '\0';
    return SBSV_OK;
}

sbsv_status sbsv_escape_str(const char* input, char** output) {
    size_t index;
    size_t length;
    size_t out_len;
    size_t out_cap;
    char* result;
    size_t* bracket_stack;
    size_t bracket_stack_count;
    size_t bracket_stack_cap;
    unsigned char* escape_bracket;

    if (input == NULL || output == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    length = strlen(input);
    out_cap = length * 2 + 1;
    if (out_cap < 16) {
        out_cap = 16;
    }

    result = (char*)malloc(out_cap);
    if (result == NULL) {
        return SBSV_ERR_ALLOC;
    }
    bracket_stack = NULL;
    bracket_stack_count = 0;
    bracket_stack_cap = 0;
    escape_bracket = NULL;
    if (length > 0) {
        escape_bracket = (unsigned char*)calloc(length, sizeof(unsigned char));
        if (escape_bracket == NULL) {
            free(result);
            return SBSV_ERR_ALLOC;
        }
    }

    for (index = 0; index < length; ++index) {
        if (input[index] == '[') {
            if (bracket_stack_count >= bracket_stack_cap) {
                size_t new_cap = (bracket_stack_cap == 0) ? 8 : (bracket_stack_cap * 2);
                size_t* new_stack = (size_t*)realloc(bracket_stack, sizeof(size_t) * new_cap);
                if (new_stack == NULL) {
                    free(bracket_stack);
                    free(escape_bracket);
                    free(result);
                    return SBSV_ERR_ALLOC;
                }
                bracket_stack = new_stack;
                bracket_stack_cap = new_cap;
            }
            bracket_stack[bracket_stack_count] = index;
            bracket_stack_count += 1;
        } else if (input[index] == ']') {
            if (bracket_stack_count == 0) {
                escape_bracket[index] = 1;
            } else {
                bracket_stack_count -= 1;
            }
        }
    }
    while (bracket_stack_count > 0) {
        bracket_stack_count -= 1;
        escape_bracket[bracket_stack[bracket_stack_count]] = 1;
    }
    free(bracket_stack);

    out_len = 0;
    result[0] = '\0';

    for (index = 0; index < length; ++index) {
        size_t escaped_len;
        const char* escaped = sbsv_escape_replacement(input[index], &escaped_len);
        sbsv_status st;

        if ((input[index] == '[' || input[index] == ']') && !escape_bracket[index]) {
            st = sbsv_append_char(&result, &out_len, &out_cap, input[index]);
        } else if (escaped != NULL) {
            st = sbsv_append_bytes(&result, &out_len, &out_cap, escaped, escaped_len);
        } else {
            st = sbsv_append_char(&result, &out_len, &out_cap, input[index]);
        }

        if (st != SBSV_OK) {
            free(escape_bracket);
            free(result);
            return st;
        }
    }

    free(escape_bracket);
    *output = result;
    return SBSV_OK;
}

sbsv_status sbsv_unescape_str(const char* input, char** output) {
    size_t length;
    size_t i;
    size_t out_len;
    char* result;
    const char* src;
    bool strict;

    if (input == NULL || output == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    src = input;
    length = strlen(input);
    strict = false;
    {
        const char* start = input;
        const char* end = input + length;
        sbsv_trim_view(&start, &end);
        if (start < end && *start == '"') {
            if (end - start < 2 || *(end - 1) != '"') {
                return SBSV_ERR_INVALID_ARG;
            }
            src = start + 1;
            length = (size_t)(end - start - 2);
            strict = true;
        }
    }

    if (strict) {
        bool escape = false;
        for (i = 0; i < length; ++i) {
            if (escape) {
                char ignored;
                if (!sbsv_unescape_char(src[i], &ignored)) {
                    return SBSV_ERR_INVALID_ARG;
                }
                escape = false;
                continue;
            }
            if (src[i] == '\\') {
                escape = true;
                continue;
            }
            if (src[i] == '"') {
                return SBSV_ERR_INVALID_ARG;
            }
        }
        if (escape) {
            return SBSV_ERR_INVALID_ARG;
        }
    }

    result = (char*)malloc(length + 1);
    if (result == NULL) {
        return SBSV_ERR_ALLOC;
    }

    out_len = 0;
    i = 0;
    while (i < length) {
        if (src[i] == '\\' && i + 1 < length) {
            bool matched;
            char unescaped;

            matched = sbsv_unescape_char(src[i + 1], &unescaped);
            if (matched) {
                result[out_len++] = unescaped;
                i += 2;
                continue;
            }
            if (strict) {
                free(result);
                return SBSV_ERR_INVALID_ARG;
            }
        } else if (src[i] == '\\' && strict) {
            free(result);
            return SBSV_ERR_INVALID_ARG;
        }

        result[out_len++] = src[i];
        i += 1;
    }

    result[out_len] = '\0';
    *output = result;
    return SBSV_OK;
}

static sbsv_status sbsv_tokenize_line_internal(const char* line, sbsv_token_list* out_tokens, int strict) {
    size_t length;
    size_t max_tokens;
    size_t pointer_bytes;
    char** items;
    void* allocation = NULL;
    char* write_cursor;
    char* token_start = NULL;
    const char* read_cursor;
    int level = 0;
    bool escape = false;
    bool quote = false;
    size_t count = 0;

    if (line == NULL || out_tokens == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    out_tokens->items = NULL;
    out_tokens->count = 0;
    out_tokens->allocation = NULL;
    length = strlen(line);
    max_tokens = length / 2 + 1;
    if (
        max_tokens > SIZE_MAX / sizeof(char*)
        || max_tokens * sizeof(char*) > SIZE_MAX - length - 1
    ) {
        return SBSV_ERR_ALLOC;
    }
    pointer_bytes = max_tokens * sizeof(char*);
    allocation = malloc(pointer_bytes + length + 1);
    if (allocation == NULL) {
        return SBSV_ERR_ALLOC;
    }
    items = (char**)allocation;
    write_cursor = (char*)allocation + pointer_bytes;

    if (
        memchr(line, '\\', length) == NULL
        && memchr(line, '"', length) == NULL
    ) {
        for (read_cursor = line; *read_cursor != '\0'; ++read_cursor) {
            char ch = *read_cursor;
            if (ch == '[') {
                level += 1;
                if (level == 1) {
                    token_start = write_cursor;
                } else {
                    *write_cursor++ = ch;
                }
            } else if (ch == ']') {
                level -= 1;
                if (level < 0) {
                    if (strict) {
                        free(allocation);
                        return SBSV_ERR_INVALID_ARG;
                    }
                    level = 0;
                    token_start = NULL;
                } else if (level == 0) {
                    const char* trimmed_start = token_start;
                    const char* trimmed_end = write_cursor;
                    size_t token_length;

                    sbsv_trim_view(&trimmed_start, &trimmed_end);
                    token_length = (size_t)(trimmed_end - trimmed_start);
                    if (trimmed_start != token_start && token_length > 0) {
                        memmove(token_start, trimmed_start, token_length);
                    }
                    items[count++] = token_start;
                    write_cursor = token_start + token_length;
                    *write_cursor++ = '\0';
                    token_start = NULL;
                } else {
                    *write_cursor++ = ch;
                }
            } else if (level > 0) {
                *write_cursor++ = ch;
            }
        }
        if (level > 0) {
            free(allocation);
            return SBSV_ERR_INVALID_ARG;
        }
        goto finished;
    }

    for (read_cursor = line; *read_cursor != '\0'; ++read_cursor) {
        char ch = *read_cursor;

        if (escape) {
            escape = false;
            *write_cursor++ = ch;
            continue;
        }
        if (ch == '\\' && level > 0) {
            escape = true;
            *write_cursor++ = ch;
            continue;
        }
        if (
            ch == '"'
            && level > 0
            && (
                quote
                || sbsv_can_start_quote(
                    token_start,
                    token_start == NULL ? 0 : (size_t)(write_cursor - token_start)
                )
            )
        ) {
            quote = !quote;
            *write_cursor++ = ch;
            continue;
        }

        if (ch == '[' && !quote) {
            level += 1;
            if (level == 1) {
                token_start = write_cursor;
            } else {
                *write_cursor++ = ch;
            }
            continue;
        }
        if (ch == ']' && !quote) {
            level -= 1;
            if (level < 0) {
                if (strict) {
                    free(allocation);
                    return SBSV_ERR_INVALID_ARG;
                }
                level = 0;
                token_start = NULL;
                continue;
            }
            if (level == 0) {
                const char* trimmed_start = token_start;
                const char* trimmed_end = write_cursor;
                size_t token_length;

                sbsv_trim_view(&trimmed_start, &trimmed_end);
                token_length = (size_t)(trimmed_end - trimmed_start);
                if (trimmed_start != token_start && token_length > 0) {
                    memmove(token_start, trimmed_start, token_length);
                }
                items[count++] = token_start;
                write_cursor = token_start + token_length;
                *write_cursor++ = '\0';
                token_start = NULL;
            } else {
                *write_cursor++ = ch;
            }
            continue;
        }

        if (level > 0) {
            *write_cursor++ = ch;
        }
    }

    if (quote || level > 0) {
        free(allocation);
        return SBSV_ERR_INVALID_ARG;
    }

finished:
    if (count == 0) {
        free(allocation);
        return SBSV_OK;
    }
    out_tokens->items = items;
    out_tokens->count = count;
    out_tokens->allocation = allocation;
    return SBSV_OK;
}

sbsv_status sbsv_tokenize_line(const char* line, sbsv_token_list* out_tokens) {
    return sbsv_tokenize_line_internal(line, out_tokens, 0);
}
sbsv_status sbsv_tokenize_line_strict(const char* line, sbsv_token_list* out_tokens) {
    return sbsv_tokenize_line_internal(line, out_tokens, 1);
}

void sbsv_free_token_list(sbsv_token_list* tokens) {
    if (tokens == NULL) {
        return;
    }

    free(tokens->allocation);
    tokens->items = NULL;
    tokens->count = 0;
    tokens->allocation = NULL;
}

void sbsv_free_string(char* value) {
    free(value);
}
