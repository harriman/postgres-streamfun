/*-------------------------------------------------------------------------
 *
 * nodeFunctionscan.h
 *
 *
 *
 * Portions Copyright (c) 1996-2010, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * $PostgreSQL: pgsql/src/include/executor/nodeFunctionscan.h,v 1.15 2010/01/02 16:58:03 momjian Exp $
 *
 *-------------------------------------------------------------------------
 */
#ifndef NODEFUNCTIONSCAN_H
#define NODEFUNCTIONSCAN_H

#include "nodes/execnodes.h"

extern FunctionScanState *ExecInitFunctionScan(FunctionScan *node, EState *estate, int eflags);
extern TupleTableSlot *ExecFunctionScan(FunctionScanState *scanstate);
extern void ExecEndFunctionScan(FunctionScanState *scanstate);
extern void ExecFunctionReScan(FunctionScanState *scanstate, ExprContext *econtext);

#endif   /* NODEFUNCTIONSCAN_H */
