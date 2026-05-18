#include "sbsv.h"

#include <stdbool.h>
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

static sbsv_status sbsv_copy_to_heap(const char* src, size_t len, char** output) {
    char* result;

    if (output == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    result = (char*)malloc(len + 1);
    if (result == NULL) {
        return SBSV_ERR_ALLOC;
    }

    if (len > 0) {
        memcpy(result, src, len);
    }
    result[len] = '\0';

    *output = result;
    return SBSV_OK;
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

static sbsv_status sbsv_append_token(sbsv_token_list* tokens, size_t* token_cap, char* token) {
    char** new_items;

    if (tokens->count >= *token_cap) {
        size_t new_cap = (*token_cap == 0) ? 4 : (*token_cap * 2);
        while (tokens->count >= new_cap) {
            new_cap *= 2;
        }
        new_items = (char**)realloc(tokens->items, sizeof(char*) * new_cap);
        if (new_items == NULL) {
            return SBSV_ERR_ALLOC;
        }
        tokens->items = new_items;
        *token_cap = new_cap;
    }

    tokens->items[tokens->count] = token;
    tokens->count += 1;
    return SBSV_OK;
}

static sbsv_status sbsv_finalize_token(const char* token_buf, size_t token_len, sbsv_token_list* out_tokens, size_t* token_cap) {
    const char* start;
    const char* end;
    char* final_token = NULL;
    sbsv_status status;

    start = token_buf;
    end = token_buf + token_len;
    sbsv_trim_view(&start, &end);

    status = sbsv_copy_to_heap(start, (size_t)(end - start), &final_token);
    if (status != SBSV_OK) {
        return status;
    }

    status = sbsv_append_token(out_tokens, token_cap, final_token);
    if (status != SBSV_OK) {
        free(final_token);
        return status;
    }

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

sbsv_status sbsv_tokenize_line(const char* line, sbsv_token_list* out_tokens) {
    int level;
    size_t length;
    size_t i;
    bool escape;
    bool quote;
    char* current;
    size_t current_len;
    size_t current_cap;
    size_t token_cap;
    sbsv_status status;

    if (line == NULL || out_tokens == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    out_tokens->items = NULL;
    out_tokens->count = 0;

    level = 0;
    length = strlen(line);
    escape = false;
    quote = false;
    current = NULL;
    current_len = 0;
    current_cap = 0;
    token_cap = 0;

    status = sbsv_append_char(&current, &current_len, &current_cap, '\0');
    if (status != SBSV_OK) {
        return status;
    }
    current_len = 0;

    for (i = 0; i < length; ++i) {
        char ch = line[i];

        if (escape) {
            escape = false;

            if (level > 0) {
                status = sbsv_append_char(&current, &current_len, &current_cap, '\\');
                if (status == SBSV_OK) {
                    status = sbsv_append_char(&current, &current_len, &current_cap, ch);
                }

                if (status != SBSV_OK) {
                    free(current);
                    sbsv_free_token_list(out_tokens);
                    return status;
                }
            }
            continue;
        }

        if (ch == '\\') {
            if (level > 0) {
                escape = true;
                continue;
            }
        }

        if (ch == '"' && level > 0 && (quote || sbsv_can_start_quote(current, current_len))) {
            quote = !quote;
            status = sbsv_append_char(&current, &current_len, &current_cap, ch);
            if (status != SBSV_OK) {
                free(current);
                sbsv_free_token_list(out_tokens);
                return status;
            }
            continue;
        }

        if (ch == '[' && !quote) {
            level += 1;
            if (level == 1) {
                if (current_len > 0) {
                    status = sbsv_finalize_token(current, current_len, out_tokens, &token_cap);
                    if (status != SBSV_OK) {
                        free(current);
                        sbsv_free_token_list(out_tokens);
                        return status;
                    }
                }
                current_len = 0;
                current[0] = '\0';
                continue;
            }
        } else if (ch == ']' && !quote) {
            level -= 1;
            if (level < 0) {
                level = 0;
                continue;
            }
            if (level == 0) {
                status = sbsv_finalize_token(current, current_len, out_tokens, &token_cap);
                if (status != SBSV_OK) {
                    free(current);
                    sbsv_free_token_list(out_tokens);
                    return status;
                }
                current_len = 0;
                current[0] = '\0';
                continue;
            }
        }

        if (level > 0) {
            status = sbsv_append_char(&current, &current_len, &current_cap, ch);
            if (status != SBSV_OK) {
                free(current);
                sbsv_free_token_list(out_tokens);
                return status;
            }
        }
    }

    if (escape && level > 0) {
        status = sbsv_append_char(&current, &current_len, &current_cap, '\\');
        if (status != SBSV_OK) {
            free(current);
            sbsv_free_token_list(out_tokens);
            return status;
        }
    }

    if (quote || level > 0) {
        free(current);
        sbsv_free_token_list(out_tokens);
        return SBSV_ERR_INVALID_ARG;
    }

    free(current);
    return SBSV_OK;
}

void sbsv_free_token_list(sbsv_token_list* tokens) {
    size_t i;

    if (tokens == NULL || tokens->items == NULL) {
        return;
    }

    for (i = 0; i < tokens->count; ++i) {
        free(tokens->items[i]);
    }

    free(tokens->items);
    tokens->items = NULL;
    tokens->count = 0;
}

void sbsv_free_string(char* value) {
    free(value);
}
