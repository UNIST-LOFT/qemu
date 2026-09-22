#ifndef SYMBOLIC_TRANSPORT_H
#define SYMBOLIC_TRANSPORT_H

#include "qemu/osdep.h"
#include "symbolic-struct.h"
#include "config.h"

typedef struct SymbolicTransport {
    Expr *expression_pool;
    Query *query_queue;
    uint8_t *branch_bitmap;
    bool external_solver;
} SymbolicTransport;

bool symbolic_transport_open(SymbolicTransport *transport,
                             const SymbolicConfig *config);
bool symbolic_transport_wait_ready(const SymbolicTransport *transport);

#endif /* SYMBOLIC_TRANSPORT_H */
