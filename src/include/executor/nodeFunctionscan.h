/*-------------------------------------------------------------------------
 *
 * nodeFunctionscan.h
 *
 *
 *
 * Portions Copyright (c) 1996-2013, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/executor/nodeFunctionscan.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef NODEFUNCTIONSCAN_H
#define NODEFUNCTIONSCAN_H

#include "nodes/execnodes.h"

extern FunctionScanState *ExecInitFunctionScan(FunctionScan *node, EState *estate, int eflags);
extern TupleTableSlot *ExecFunctionScan(FunctionScanState *scanstate);
extern void ExecEndFunctionScan(FunctionScanState *scanstate);
extern void ExecReScanFunctionScan(FunctionScanState *scanstate);

#endif   /* NODEFUNCTIONSCAN_H */
