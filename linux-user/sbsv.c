#include "sbsv.h"

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

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
        case '/':
            *out_len = 2;
            return "\\/";
        case '\\':
            *out_len = 2;
            return "\\\\";
        case '[':
            *out_len = 2;
            return "\\[";
        case ']':
            *out_len = 2;
            return "\\]";
        case ',':
            *out_len = 2;
            return "\\,";
        case ':':
            *out_len = 2;
            return "\\:";
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
        case '/':
            *out_raw = '/';
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
        case ',':
            *out_raw = ',';
            return true;
        case ':':
            *out_raw = ':';
            return true;
        default:
            return false;
    }
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
    out_len = 0;
    result[0] = '\0';

    for (index = 0; index < length; ++index) {
        size_t escaped_len;
        const char* escaped = sbsv_escape_replacement(input[index], &escaped_len);
        sbsv_status st;

        if (escaped != NULL) {
            st = sbsv_append_bytes(&result, &out_len, &out_cap, escaped, escaped_len);
        } else {
            st = sbsv_append_char(&result, &out_len, &out_cap, input[index]);
        }

        if (st != SBSV_OK) {
            free(result);
            return st;
        }
    }

    *output = result;
    return SBSV_OK;
}

sbsv_status sbsv_unescape_str(const char* input, char** output) {
    size_t length;
    size_t i;
    size_t out_len;
    char* result;

    if (input == NULL || output == NULL) {
        return SBSV_ERR_INVALID_ARG;
    }

    length = strlen(input);
    result = (char*)malloc(length + 1);
    if (result == NULL) {
        return SBSV_ERR_ALLOC;
    }

    out_len = 0;
    i = 0;
    while (i < length) {
        if (input[i] == '\\' && i + 1 < length) {
            bool matched;
            char unescaped;

            matched = sbsv_unescape_char(input[i + 1], &unescaped);
            if (matched) {
                result[out_len++] = unescaped;
                i += 2;
                continue;
            }
        }

        result[out_len++] = input[i];
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
            char unescaped;

            escape = false;

            if (level > 0) {
                if (sbsv_unescape_char(ch, &unescaped)) {
                    status = sbsv_append_char(&current, &current_len, &current_cap, unescaped);
                } else {
                    status = sbsv_append_char(&current, &current_len, &current_cap, '\\');
                    if (status == SBSV_OK) {
                        status = sbsv_append_char(&current, &current_len, &current_cap, ch);
                    }
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
            escape = true;
            continue;
        }

        if (ch == '[') {
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
        } else if (ch == ']') {
            level -= 1;
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
