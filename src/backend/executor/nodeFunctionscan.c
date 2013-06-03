/*-------------------------------------------------------------------------
 *
 * nodeFunctionscan.c
 *	  Support routines for scanning RangeFunctions (functions in rangetable).
 *
 * Portions Copyright (c) 1996-2009, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/executor/nodeFunctionscan.c,v 1.52 2009/06/11 14:48:57 momjian Exp $
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
FunctionMaterial(ScanState *node)
{
	FunctionScanState	*scanstate = (FunctionScanState *) node;
	TupleTableSlot		*slot = scanstate->ss.ss_ScanTupleSlot;
	bool forward = ScanDirectionIsForward(scanstate->ss.ps.state->es_direction);

	ExecClearTuple(slot);

	/*
	 * Try to fetch a tuple from tuplestore.
	 */
	if (scanstate->tuplestorestate)
	{
		Tuplestorestate	*tuplestorestate = scanstate->tuplestorestate;
		bool			eof_tuplestore = tuplestore_ateof(tuplestorestate);

		/*
		 * If we are not at the end of the tuplestore, or are going backwards,
		 * try to fetch a tuple from tuplestore.
		 */
		if (!forward && eof_tuplestore)
		{
			if (!scanstate->eof_underlying)
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
			if (tuplestore_gettupleslot(tuplestorestate, forward, false, slot))
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
	if (!scanstate->eof_underlying)
	{
		ExprContext		*econtext = scanstate->funcexprcontext;
		MemoryContext	oldcontext;

		/* Switch to short-lived context for calling the function. */
		oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

		if (!ExecMaterializeTableFunction(scanstate, econtext, slot))
			scanstate->eof_underlying = true;

		/* Switch back to caller's context. */
		MemoryContextSwitchTo(oldcontext);
	}

	Assert(scanstate->eof_underlying == slot->tts_isempty);
	return slot;
}

/*
 * FunctionNext -- Forward scan, once only
 */
static TupleTableSlot *
FunctionNext(ScanState *node)
{
	FunctionScanState	*scanstate = (FunctionScanState *) node;
	TupleTableSlot		*slot = scanstate->ss.ss_ScanTupleSlot;
	ExprContext			*econtext = scanstate->funcexprcontext;
	MemoryContext		oldcontext;
	Datum				result;
	ExprDoneCond		isDone;
	bool				isNull;

	Assert(ScanDirectionIsForward(scanstate->ss.ps.state->es_direction));

	/* Clear out any previous result. */
	ExecClearTuple(slot);

	/* Reset the per-tuple memory context. */
	ResetExprContext(econtext);

	/* Return empty slot if no more data. */
	if (scanstate->eof_underlying)
		return slot;

	/* Switch to short-lived context for calling the function or expression. */
	oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

	/* Get function's next result value. */
	result = ExecEvalExpr(scanstate->funcexpr, econtext, &isNull, &isDone);

	/* If result is a singleton, or no more data, we'll return EOD next time. */
	if (isDone != ExprMultipleResult)
		scanstate->eof_underlying = true;

	if (isDone != ExprEndResult)
	{
		/* 
		 * If result is of composite or RECORD type, fail if the actual tuple 
		 * format is incompatible with the output slot's expected tupdesc.
		 * Skip if expr is a function, because ExecEvalFunc or ExecEvalSRF 
		 * checked this already.
		 */
		if (!isNull &&
			scanstate->returnsTuple &&
			!IsA(scanstate->funcexpr, FuncExprState))
			ExecVerifyReturnedRowType((Expr *) scanstate->funcexpr, 
									  result,
									  slot->tts_tupleDescriptor, 
									  &scanstate->returnedTypeId,
									  &scanstate->returnedTypMod);

		/* Store result in slot. */
		ExecStoreSlotTupleDatum(slot, result, isNull, scanstate->returnsTuple);
	}

	/* Restore caller's context. */
	MemoryContextSwitchTo(oldcontext);

	return slot;
}

/* ----------------------------------------------------------------
 *		ExecFunctionScan(scanstate)
 *
 *		Scans the function sequentially and returns the next qualifying
 *		tuple.
 *		We call the ExecScan() routine and pass it the appropriate
 *		access method functions.
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecFunctionScan(FunctionScanState *scanstate)
{
	if (scanstate->materialize)
		return ExecScan(&scanstate->ss, FunctionMaterial);
	else
		return ExecScan(&scanstate->ss, FunctionNext);
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

	/*
	 * FunctionScan should not have any children.
	 */
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
							&scanstate->returnsTuple);

	/*
	 * If type is RECORD, build tupdesc from the column names and types given
	 * explicitly in the query:  FROM f(args) AS alias(colname, coltype, ...).
	 *
	 * If the resultcol lists are empty, we build a 0-column tuple descriptor,
	 * and the function must return columnless tuples.
	 */
	if (scanstate->returnsTuple && !tupdesc)
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

	/* No actual result row type has been validated yet. */
	scanstate->returnedTypeId = InvalidOid;
	scanstate->returnedTypMod = 0;

	/* Should we save the function results in a tuplestore? */
	scanstate->tuplestorestate = NULL;
	if (eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_REWIND))
	{
		scanstate->materialize = true;
		if (eflags & EXEC_FLAG_BACKWARD)
			scanstate->randomAccess = true;
	}

	/* Initialize the function expression. */
	scanstate->funcexpr = ExecInitTableFunction((Expr *) node->funcexpr,
												(PlanState *) scanstate,
												scanstate->funcexprcontext,
												tupdesc,
												scanstate->returnsTuple,
												scanstate->randomAccess);

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
ExecEndFunctionScan(FunctionScanState *scanstate)
{
	ExecFreeExprContext(&scanstate->ss.ps);

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(scanstate->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(scanstate->ss.ss_ScanTupleSlot);

	/* Free the tuplestore. */
	if (scanstate->tuplestorestate)
		tuplestore_end(scanstate->tuplestorestate);
}

/* ----------------------------------------------------------------
 *		ExecFunctionReScan
 *
 *		Rescans the relation.
 * ----------------------------------------------------------------
 */
void
ExecFunctionReScan(FunctionScanState *scanstate, ExprContext *econtext)
{
	ExecClearTuple(scanstate->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(scanstate->ss.ss_ScanTupleSlot);

	scanstate->ss.ps.ps_TupFromTlist = false;

	/*
	 * Here we have a choice whether to drop the tuplestore (and recompute the
	 * function outputs) or just rescan it.  We must recompute if the
	 * expression contains parameters, else we rescan.	XXX maybe we should
	 * recompute if the function is volatile?
	 */
	if (scanstate->ss.ps.chgParam != NULL)
	{
		/* Discard any materialized results. */
		if (scanstate->tuplestorestate)
			tuplestore_clear(scanstate->tuplestorestate);

		/* 
		 * Reset any set-returning subexpressions that were expecting to be
		 * called again in ExprMultipleResult protocol.  They must start fresh 
		 * with new arguments the next time we call.
		 */
		ReScanExprContext(scanstate->funcexprcontext);
		scanstate->eof_underlying = false;
	}

	/* 
	 * Rescan materialized results.  Don't disturb the expr.  At the end of 
	 * the tuplestore, if the expr hasn't yet returned all of its result 
	 * tuples, we'll pick up where we left off, and resume calling the expr 
	 * for further results.
	 */
	else if (scanstate->materialize)
	{
		if (scanstate->tuplestorestate)
			tuplestore_rescan(scanstate->tuplestorestate);
	}

 	/* 
 	 * Results are being passed through directly, not saved in tuplestore.
 	 * We'll re-evaluate expr so it will produce its (same?) results again.
 	 */
	else
	{
		/* Reset any incomplete set-returning subexpressions. */
		ReScanExprContext(scanstate->funcexprcontext);
		scanstate->eof_underlying = false;
	}
}
