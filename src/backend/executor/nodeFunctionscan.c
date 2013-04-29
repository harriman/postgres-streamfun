/*-------------------------------------------------------------------------
 *
 * nodeFunctionscan.c
 *	  Support routines for scanning RangeFunctions (functions in rangetable).
 *
 * Portions Copyright (c) 1996-2008, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/executor/nodeFunctionscan.c,v 1.45.2.1 2008/02/29 02:49:43 neilc Exp $
 *
 *-------------------------------------------------------------------------
 */
/*
 * INTERFACE ROUTINES
 *		ExecFunctionScan		scans a function.
 *		ExecFunctionNext		retrieve next tuple in sequential order.
 *		ExecInitFunctionScan	creates and initializes a functionscan node.
 *		ExecEndFunctionScan		releases any storage allocated.
 *		ExecFunctionReScan		rescans the function
 */
#include "postgres.h"

#include "executor/nodeFunctionscan.h"
#include "funcapi.h"
#include "utils/memutils.h"		/* MemoryContextReset */


/* ----------------------------------------------------------------
 *						Scan Support
 * ----------------------------------------------------------------
 */
/* ----------------------------------------------------------------
 *		FunctionMaterial
 *		FunctionNext
 *
 *		This is a workhorse for ExecFunctionScan
 * ----------------------------------------------------------------
 */
static TupleTableSlot *
FunctionMaterial(ScanState *scanState)
{
	FunctionScanState *node = (FunctionScanState *) scanState;
	TupleTableSlot *slot = node->ss.ss_ScanTupleSlot;
	bool		forward = ScanDirectionIsForward(node->ss.ps.state->es_direction);

	ExecClearTuple(slot);

	/*
	 * Try to fetch a tuple from tuplestore.
	 */
	if (node->tuplestorestate)
	{
		Tuplestorestate *tuplestorestate = node->tuplestorestate;
		bool		eof_tuplestore = tuplestore_ateof(tuplestorestate);

		/*
		 * If we are not at the end of the tuplestore, or are going backwards,
		 * try to fetch a tuple from tuplestore.
		 */
		if (!forward && eof_tuplestore)
		{
			if (!node->eof_underlying)
			{
				/*
				 * When reversing direction at tuplestore EOF, the first
				 * gettupleslot call will fetch the last-added tuple; but we
				 * want to return the one before that, if possible. So do an
				 * extra fetch.
				 */
				if (!tuplestore_advance(tuplestorestate, forward))
					return slot;	/* the tuplestore must be empty */
			}
			eof_tuplestore = false;
		}

		/* Return next tuple (in the current scan direction) from tuplestore. */
		if (!eof_tuplestore)
		{
			if (tuplestore_gettupleslot(tuplestorestate, forward, slot))
				return slot;

			/*
			 * Hit beginning of tuplestore reading backwards. Return empty
			 * slot.
			 */
			if (!forward)
				return slot;
		}
	}

	/*
	 * Get next tuple from function.  Also gets a tuplestore if we don't
	 * already have one.
	 */
	if (!node->eof_underlying)
	{
		ExprContext *econtext = node->funcexprcontext;
		MemoryContext oldcontext;

		/* Switch to short-lived context for calling the function. */
		oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

		if (!ExecMaterializeTableFunction(slot,
										  node->returnstuple,
										  &node->tuplestorestate,
										  node->funcexpr,
										  econtext))
			node->eof_underlying = true;

		/* Switch back to caller's context. */
		MemoryContextSwitchTo(oldcontext);
	}

	Assert(node->eof_underlying == slot->tts_isempty);
	return slot;
}

/*
 * FunctionNext -- Forward scan, once only
 */
static TupleTableSlot *
FunctionNext(ScanState *scanState)
{
	FunctionScanState *node = (FunctionScanState *) scanState;
	TupleTableSlot *slot = node->ss.ss_ScanTupleSlot;
	ExprContext *econtext = node->funcexprcontext;
	MemoryContext oldcontext;
	Datum		result;
	ExprDoneCond isDone;
	bool		isNull;

	Assert(ScanDirectionIsForward(node->ss.ps.state->es_direction));

	/* Clear out any previous result. */
	ExecClearTuple(slot);

	/* Reset the per-tuple memory context. */
	ResetExprContext(econtext);

	/* Return empty slot if no more data. */
	if (node->eof_underlying)
		return slot;

	/* Switch to short-lived context for calling the function or expression. */
	oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

	/* Get function's next result value. */
	result = ExecEvalExpr(node->funcexpr, econtext, &isNull, &isDone);

	/* If result is a singleton, or no more data, we'll return EOD next time. */
	if (isDone != ExprMultipleResult)
		node->eof_underlying = true;

	/* Store result in slot. */
	if (isDone != ExprEndResult)
		ExecStoreSlotTupleDatum(slot, result, isNull, node->returnstuple);

	/* Restore caller's context. */
	MemoryContextSwitchTo(oldcontext);

	return slot;
}

/* ----------------------------------------------------------------
 *		ExecFunctionScan(node)
 *
 *		Scans the function sequentially and returns the next qualifying
 *		tuple.
 *		We call the ExecScan() routine and pass it the appropriate
 *		access method functions.
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecFunctionScan(FunctionScanState *node)
{
	if (node->materialize)
		return ExecScan(&node->ss, FunctionMaterial);
	else
		return ExecScan(&node->ss, FunctionNext);
}

/* ----------------------------------------------------------------
 *		ExecInitFunctionScan
 * ----------------------------------------------------------------
 */
FunctionScanState *
ExecInitFunctionScan(FunctionScan *node, EState *estate, int eflags)
{
	FunctionScanState *scanstate;
	TupleDesc	tupdesc;
	const char *scalarattname;

	/* check for unsupported flags */
	Assert(!(eflags & EXEC_FLAG_MARK));

	/* FunctionScan should not have any children. */
	Assert(outerPlan(node) == NULL);
	Assert(innerPlan(node) == NULL);

	/*
	 * create new ScanState for node
	 */
	scanstate = makeNode(FunctionScanState);
	scanstate->ss.ps.plan = (Plan *) node;
	scanstate->ss.ps.state = estate;

	/*
	 * Create two expression contexts: one for evaluating the projection and
	 * quals, and another for the function expression.	We separate them so
	 * each can have its own list of ExprContext callback functions.  In case
	 * the projection contains more than one set-valued expression, and one
	 * refuses to restart, then ExecTargetList can call ShutdownExprContext to
	 * reset the others... we don't want this to affect our table function.
	 */
	ExecAssignExprContext(estate, &scanstate->ss.ps);
	scanstate->funcexprcontext = CreateExprContext(estate);

#define FUNCTIONSCAN_NSLOTS 2

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &scanstate->ss.ps);
	ExecInitScanTupleSlot(estate, &scanstate->ss);

	/*
	 * initialize child expressions
	 */
	scanstate->ss.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->scan.plan.targetlist,
					 (PlanState *) scanstate);
	scanstate->ss.ps.qual = (List *)
		ExecInitExpr((Expr *) node->scan.plan.qual,
					 (PlanState *) scanstate);

	/*
	 * Build tuple descriptor for the expected result of the expression. Find
	 * out whether the result will be a scalar or composite type.
	 */
	scalarattname = NULL;
	if (node->funccolnames)
		scalarattname = strVal(linitial(node->funccolnames));

	get_expr_result_tupdesc((Expr *) node->funcexpr,
							scalarattname,
							&tupdesc,
							&scanstate->returnstuple);

	/*
	 * If type is RECORD, build tupdesc from the column names and types given
	 * explicitly in the query:  FROM f(args) AS alias(colname, coltype, ...).
	 *
	 * If the resultcol lists are empty, we build a 0-column tuple descriptor,
	 * and the function must return columnless tuples.
	 */
	if (scanstate->returnstuple && !tupdesc)
	{
		tupdesc = BuildDescFromLists(node->funccolnames,
									 node->funccoltypes,
									 node->funccoltypmods);
		BlessTupleDesc(tupdesc);
	}
	else if (!tupdesc)
	{
		/* crummy error message, but parser should have caught this */
		elog(ERROR, "function in FROM has unsupported return type");
	}

	ExecAssignScanType(&scanstate->ss, tupdesc);

	/*
	 * Should we save the function results in a tuplestore?
	 */
	scanstate->tuplestorestate = NULL;
	if (eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_REWIND))
		scanstate->materialize = true;

	/*
	 * Initialize the function expression.
	 */
	scanstate->funcexpr = ExecInitTableFunction((Expr *) node->funcexpr,
												(PlanState *) scanstate,
												scanstate->funcexprcontext,
												tupdesc,
												scanstate->returnstuple);

	/*
	 * Initialize result tuple type and projection info.
	 */
	ExecAssignResultTypeFromTL(&scanstate->ss.ps);
	ExecAssignScanProjectionInfo(&scanstate->ss);

	return scanstate;
}

int
ExecCountSlotsFunctionScan(FunctionScan *node)
{
	return ExecCountSlotsNode(outerPlan(node)) +
		ExecCountSlotsNode(innerPlan(node)) +
		FUNCTIONSCAN_NSLOTS;
}

/* ----------------------------------------------------------------
 *		ExecEndFunctionScan
 *
 *		frees any storage allocated through C routines.
 * ----------------------------------------------------------------
 */
void
ExecEndFunctionScan(FunctionScanState *node)
{
	ExecFreeExprContext(&node->ss.ps);

	/* clean out the tuple table */
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->ss.ss_ScanTupleSlot);

	/* Free the tuplestore. */
	if (node->tuplestorestate)
		tuplestore_end(node->tuplestorestate);
}

/* ----------------------------------------------------------------
 *		ExecFunctionReScan
 *
 *		Rescans the relation.
 * ----------------------------------------------------------------
 */
void
ExecFunctionReScan(FunctionScanState *node, ExprContext *exprCtxt)
{
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->ss.ss_ScanTupleSlot);

	node->ss.ps.ps_TupFromTlist = false;

	/* Reset the function expression. */
	ReScanExprContext(node->funcexprcontext);

	/*
	 * If we haven't materialized yet, just return.
	 */
	if (!node->tuplestorestate)
		node->eof_underlying = false;

	/*
	 * Here we have a choice whether to drop the tuplestore (and recompute the
	 * function outputs) or just rescan it.  We must recompute if the
	 * expression contains parameters, else we rescan.	XXX maybe we should
	 * recompute if the function is volatile?
	 */
	else if (node->ss.ps.chgParam != NULL)
	{
		tuplestore_end(node->tuplestorestate);
		node->tuplestorestate = NULL;
		node->eof_underlying = false;
	}
	else
		tuplestore_rescan(node->tuplestorestate);
}
