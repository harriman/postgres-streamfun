/*-------------------------------------------------------------------------
 *
 * execQual.c
 *	  Routines to evaluate qualification and targetlist expressions
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execQual.c
 *
 *-------------------------------------------------------------------------
 */
/*
 *	 INTERFACE ROUTINES
 *		ExecEvalExpr	- (now a macro) evaluate an expression, return a datum
 *		ExecEvalExprSwitchContext - same, but switch into eval memory context
 *		ExecQual		- return true/false if qualification is satisfied
 *		ExecProject		- form a new tuple by projecting the given tuple
 *
 *	 NOTES
 *		The more heavily used ExecEvalExpr routines, such as ExecEvalScalarVar,
 *		are hotspots. Making these faster will speed up the entire system.
 *
 *		ExecProject() is used to make tuple projections.  Rather then
 *		trying to speed it up, the execution plan should be pre-processed
 *		to facilitate attribute sharing between nodes wherever possible,
 *		instead of doing needless copying.	-cim 5/31/91
 *
 *		During expression evaluation, we check_stack_depth only at function
 *		invocations (ExecEvalFunc, ExecEvalFuncSRF, etc) rather than at every
 *		single node.  This is a compromise that trades off precision of the
 *		stack limit setting to gain speed.
 */

#include "postgres.h"

#include "access/nbtree.h"
#include "access/tupconvert.h"
#include "catalog/pg_type.h"
#include "commands/typecmds.h"
#include "executor/execdebug.h"
#include "executor/nodeSubplan.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/planner.h"
#include "parser/parse_coerce.h"
#include "pgstat.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/typcache.h"
#include "utils/xml.h"


/* static function decls */
static Datum ExecEvalArrayRef(ArrayRefExprState *astate,
				 ExprContext *econtext,
				 bool *isNull, ExprDoneCond *isDone);
static bool isAssignmentIndirectionExpr(ExprState *exprstate);
static Datum ExecEvalAggref(AggrefExprState *aggref,
			   ExprContext *econtext,
			   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalWindowFunc(WindowFuncExprState *wfunc,
				   ExprContext *econtext,
				   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalScalarVar(ExprState *exprstate, ExprContext *econtext,
				  bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalScalarVarFast(ExprState *exprstate, ExprContext *econtext,
					  bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalWholeRowVar(WholeRowVarExprState *wrvstate,
					ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalWholeRowFast(WholeRowVarExprState *wrvstate,
					 ExprContext *econtext,
					 bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalWholeRowSlow(WholeRowVarExprState *wrvstate,
					 ExprContext *econtext,
					 bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalConst(ExprState *exprstate, ExprContext *econtext,
			  bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalParamExec(ExprState *exprstate, ExprContext *econtext,
				  bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalParamExtern(ExprState *exprstate, ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone);
static void ShutdownFuncExpr(Datum arg);
static TupleDesc get_cached_rowtype(Oid type_id, int32 typmod,
				   TupleDesc *cache_field, ExprContext *econtext);
static void ShutdownTupleDescRef(Datum arg);
static void tupledesc_match(Expr *expr, TupleDesc dst_tupdesc,
				TupleDesc src_tupdesc);
static Datum ExecEvalFuncDematerialize(FuncExprState *fcache,
						  ExprContext *econtext, bool *isNull,
						  ExprDoneCond *isDone);
static Datum ExecEvalFuncSRF(FuncExprState *fcache, ExprContext *econtext,
				bool *isNull, ExprDoneCond *isDone);
static void init_fcache(Oid foid, Oid input_collation, FuncExprState *fcache,
				ExprContext *econtext);
static ExprDoneCond ExecEvalFuncArgs(FunctionCallInfo fcinfo,
				 List *argList, ExprContext *econtext);
static Datum ExecEvalFunc(FuncExprState *fcache, ExprContext *econtext,
			 bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalFuncSimple2(FuncExprState *fcache, ExprContext *econtext,
				   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalFuncSimpleN(FuncExprState *fcache, ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalDistinct(FuncExprState *fcache, ExprContext *econtext,
				 bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalScalarArrayOp(ScalarArrayOpExprState *sstate,
					  ExprContext *econtext,
					  bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalNot(BoolExprState *notclause, ExprContext *econtext,
			bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalOr(BoolExprState *orExpr, ExprContext *econtext,
		   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalAnd(BoolExprState *andExpr, ExprContext *econtext,
			bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalConvertRowtype(ConvertRowtypeExprState *cstate,
					   ExprContext *econtext,
					   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalCase(CaseExprState *caseExpr, ExprContext *econtext,
			 bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalCaseTestExpr(ExprState *exprstate,
					 ExprContext *econtext,
					 bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalArray(ArrayExprState *astate,
			  ExprContext *econtext,
			  bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalRow(RowExprState *rstate,
			ExprContext *econtext,
			bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalRowCompare(RowCompareExprState *rstate,
				   ExprContext *econtext,
				   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalCoalesce(CoalesceExprState *coalesceExpr,
				 ExprContext *econtext,
				 bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalMinMax(MinMaxExprState *minmaxExpr,
			   ExprContext *econtext,
			   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalXml(XmlExprState *xmlExpr, ExprContext *econtext,
			bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalNullIf(FuncExprState *nullIfExpr,
			   ExprContext *econtext,
			   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalNullTest(NullTestState *nstate,
				 ExprContext *econtext,
				 bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalBooleanTest(GenericExprState *bstate,
					ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalCoerceToDomain(CoerceToDomainState *cstate,
					   ExprContext *econtext,
					   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalCoerceToDomainValue(ExprState *exprstate,
							ExprContext *econtext,
							bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalFieldSelect(FieldSelectState *fstate,
					ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalFieldStore(FieldStoreState *fstate,
				   ExprContext *econtext,
				   bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalRelabelType(GenericExprState *exprstate,
					ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalCoerceViaIO(CoerceViaIOState *iostate,
					ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalArrayCoerceExpr(ArrayCoerceExprState *astate,
						ExprContext *econtext,
						bool *isNull, ExprDoneCond *isDone);
static Datum ExecEvalCurrentOfExpr(ExprState *exprstate, ExprContext *econtext,
					  bool *isNull, ExprDoneCond *isDone);


/* ----------------------------------------------------------------
 *		ExecEvalExpr routines
 *
 *		Recursively evaluate a targetlist or qualification expression.
 *
 * Each of the following routines having the signature
 *		Datum ExecEvalFoo(ExprState *expression,
 *						  ExprContext *econtext,
 *						  bool *isNull,
 *						  ExprDoneCond *isDone);
 * is responsible for evaluating one type or subtype of ExprState node.
 * They are normally called via the ExecEvalExpr macro, which makes use of
 * the function pointer set up when the ExprState node was built by
 * ExecInitExpr.  (In some cases, we change this pointer later to avoid
 * re-executing one-time overhead.)
 *
 * Note: for notational simplicity we declare these functions as taking the
 * specific type of ExprState that they work on.  This requires casting when
 * assigning the function pointer in ExecInitExpr.	Be careful that the
 * function signature is declared correctly, because the cast suppresses
 * automatic checking!
 *
 *
 * All these functions share this calling convention:
 *
 * Inputs:
 *		expression: the expression state tree to evaluate
 *		econtext: evaluation context information
 *
 * Outputs:
 *		return value: Datum value of result
 *		*isNull: set to TRUE if result is NULL (actual return value is
 *				 meaningless if so); set to FALSE if non-null result
 *		*isDone: set to indicator of set-result status
 *
 * A caller that can only accept a singleton (non-set) result should pass
 * NULL for isDone; if the expression computes a set result then an error
 * will be reported via ereport.  If the caller does pass an isDone pointer
 * then *isDone is set to one of these three states:
 *		ExprSingleResult		singleton result (not a set)
 *		ExprMultipleResult		return value is one element of a set
 *		ExprEndResult			there are no more elements in the set
 * When ExprMultipleResult is returned, the caller should invoke
 * ExecEvalExpr() repeatedly until ExprEndResult is returned.  ExprEndResult
 * is returned after the last real set element.  For convenience isNull will
 * always be set TRUE when ExprEndResult is returned, but this should not be
 * taken as indicating a NULL element of the set.  Note that these return
 * conventions allow us to distinguish among a singleton NULL, a NULL element
 * of a set, and an empty set.
 *
 * The caller should already have switched into the temporary memory
 * context econtext->ecxt_per_tuple_memory.  The convenience entry point
 * ExecEvalExprSwitchContext() is provided for callers who don't prefer to
 * do the switch in an outer loop.	We do not do the switch in these routines
 * because it'd be a waste of cycles during nested expression evaluation.
 * ----------------------------------------------------------------
 */


/*----------
 *	  ExecEvalArrayRef
 *
 *	   This function takes an ArrayRef and returns the extracted Datum
 *	   if it's a simple reference, or the modified array value if it's
 *	   an array assignment (i.e., array element or slice insertion).
 *
 * NOTE: if we get a NULL result from a subscript expression, we return NULL
 * when it's an array reference, or raise an error when it's an assignment.
 *
 * NOTE: we deliberately refrain from applying DatumGetArrayTypeP() here,
 * even though that might seem natural, because this code needs to support
 * both varlena arrays and fixed-length array types.  DatumGetArrayTypeP()
 * only works for the varlena kind.  The routines we call in arrayfuncs.c
 * have to know the difference (that's what they need refattrlength for).
 *----------
 */
static Datum
ExecEvalArrayRef(ArrayRefExprState *astate,
				 ExprContext *econtext,
				 bool *isNull,
				 ExprDoneCond *isDone)
{
	ArrayRef   *arrayRef = (ArrayRef *) astate->xprstate.expr;
	ArrayType  *array_source;
	ArrayType  *resultArray;
	bool		isAssignment = (arrayRef->refassgnexpr != NULL);
	bool		eisnull;
	ListCell   *l;
	int			i = 0,
				j = 0;
	IntArray	upper,
				lower;
	int		   *lIndex;

	array_source = (ArrayType *)
		DatumGetPointer(ExecEvalExpr(astate->refexpr,
									 econtext,
									 isNull,
									 isDone));

	/*
	 * If refexpr yields NULL, and it's a fetch, then result is NULL. In the
	 * assignment case, we'll cons up something below.
	 */
	if (*isNull)
	{
		if (isDone && *isDone == ExprEndResult)
			return (Datum) NULL;	/* end of set result */
		if (!isAssignment)
			return (Datum) NULL;
	}

	foreach(l, astate->refupperindexpr)
	{
		ExprState  *eltstate = (ExprState *) lfirst(l);

		if (i >= MAXDIM)
			ereport(ERROR,
					(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
					 errmsg("number of array dimensions (%d) exceeds the maximum allowed (%d)",
							i + 1, MAXDIM)));

		upper.indx[i++] = DatumGetInt32(ExecEvalExpr(eltstate,
													 econtext,
													 &eisnull,
													 NULL));
		/* If any index expr yields NULL, result is NULL or error */
		if (eisnull)
		{
			if (isAssignment)
				ereport(ERROR,
						(errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
				  errmsg("array subscript in assignment must not be null")));
			*isNull = true;
			return (Datum) NULL;
		}
	}

	if (astate->reflowerindexpr != NIL)
	{
		foreach(l, astate->reflowerindexpr)
		{
			ExprState  *eltstate = (ExprState *) lfirst(l);

			if (j >= MAXDIM)
				ereport(ERROR,
						(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
						 errmsg("number of array dimensions (%d) exceeds the maximum allowed (%d)",
								j + 1, MAXDIM)));

			lower.indx[j++] = DatumGetInt32(ExecEvalExpr(eltstate,
														 econtext,
														 &eisnull,
														 NULL));
			/* If any index expr yields NULL, result is NULL or error */
			if (eisnull)
			{
				if (isAssignment)
					ereport(ERROR,
							(errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
							 errmsg("array subscript in assignment must not be null")));
				*isNull = true;
				return (Datum) NULL;
			}
		}
		/* this can't happen unless parser messed up */
		if (i != j)
			elog(ERROR, "upper and lower index lists are not same length");
		lIndex = lower.indx;
	}
	else
		lIndex = NULL;

	if (isAssignment)
	{
		Datum		sourceData;
		Datum		save_datum;
		bool		save_isNull;

		/*
		 * We might have a nested-assignment situation, in which the
		 * refassgnexpr is itself a FieldStore or ArrayRef that needs to
		 * obtain and modify the previous value of the array element or slice
		 * being replaced.	If so, we have to extract that value from the
		 * array and pass it down via the econtext's caseValue.  It's safe to
		 * reuse the CASE mechanism because there cannot be a CASE between
		 * here and where the value would be needed, and an array assignment
		 * can't be within a CASE either.  (So saving and restoring the
		 * caseValue is just paranoia, but let's do it anyway.)
		 *
		 * Since fetching the old element might be a nontrivial expense, do it
		 * only if the argument appears to actually need it.
		 */
		save_datum = econtext->caseValue_datum;
		save_isNull = econtext->caseValue_isNull;

		if (isAssignmentIndirectionExpr(astate->refassgnexpr))
		{
			if (*isNull)
			{
				/* whole array is null, so any element or slice is too */
				econtext->caseValue_datum = (Datum) 0;
				econtext->caseValue_isNull = true;
			}
			else if (lIndex == NULL)
			{
				econtext->caseValue_datum = array_ref(array_source, i,
													  upper.indx,
													  astate->refattrlength,
													  astate->refelemlength,
													  astate->refelembyval,
													  astate->refelemalign,
												&econtext->caseValue_isNull);
			}
			else
			{
				resultArray = array_get_slice(array_source, i,
											  upper.indx, lower.indx,
											  astate->refattrlength,
											  astate->refelemlength,
											  astate->refelembyval,
											  astate->refelemalign);
				econtext->caseValue_datum = PointerGetDatum(resultArray);
				econtext->caseValue_isNull = false;
			}
		}
		else
		{
			/* argument shouldn't need caseValue, but for safety set it null */
			econtext->caseValue_datum = (Datum) 0;
			econtext->caseValue_isNull = true;
		}

		/*
		 * Evaluate the value to be assigned into the array.
		 */
		sourceData = ExecEvalExpr(astate->refassgnexpr,
								  econtext,
								  &eisnull,
								  NULL);

		econtext->caseValue_datum = save_datum;
		econtext->caseValue_isNull = save_isNull;

		/*
		 * For an assignment to a fixed-length array type, both the original
		 * array and the value to be assigned into it must be non-NULL, else
		 * we punt and return the original array.
		 */
		if (astate->refattrlength > 0)	/* fixed-length array? */
			if (eisnull || *isNull)
				return PointerGetDatum(array_source);

		/*
		 * For assignment to varlena arrays, we handle a NULL original array
		 * by substituting an empty (zero-dimensional) array; insertion of the
		 * new element will result in a singleton array value.	It does not
		 * matter whether the new element is NULL.
		 */
		if (*isNull)
		{
			array_source = construct_empty_array(arrayRef->refelemtype);
			*isNull = false;
		}

		if (lIndex == NULL)
			resultArray = array_set(array_source, i,
									upper.indx,
									sourceData,
									eisnull,
									astate->refattrlength,
									astate->refelemlength,
									astate->refelembyval,
									astate->refelemalign);
		else
			resultArray = array_set_slice(array_source, i,
										  upper.indx, lower.indx,
								   (ArrayType *) DatumGetPointer(sourceData),
										  eisnull,
										  astate->refattrlength,
										  astate->refelemlength,
										  astate->refelembyval,
										  astate->refelemalign);
		return PointerGetDatum(resultArray);
	}

	if (lIndex == NULL)
		return array_ref(array_source, i, upper.indx,
						 astate->refattrlength,
						 astate->refelemlength,
						 astate->refelembyval,
						 astate->refelemalign,
						 isNull);
	else
	{
		resultArray = array_get_slice(array_source, i,
									  upper.indx, lower.indx,
									  astate->refattrlength,
									  astate->refelemlength,
									  astate->refelembyval,
									  astate->refelemalign);
		return PointerGetDatum(resultArray);
	}
}

/*
 * Helper for ExecEvalArrayRef: is expr a nested FieldStore or ArrayRef
 * that might need the old element value passed down?
 *
 * (We could use this in ExecEvalFieldStore too, but in that case passing
 * the old value is so cheap there's no need.)
 */
static bool
isAssignmentIndirectionExpr(ExprState *exprstate)
{
	if (exprstate == NULL)
		return false;			/* just paranoia */
	if (IsA(exprstate, FieldStoreState))
	{
		FieldStore *fstore = (FieldStore *) exprstate->expr;

		if (fstore->arg && IsA(fstore->arg, CaseTestExpr))
			return true;
	}
	else if (IsA(exprstate, ArrayRefExprState))
	{
		ArrayRef   *arrayRef = (ArrayRef *) exprstate->expr;

		if (arrayRef->refexpr && IsA(arrayRef->refexpr, CaseTestExpr))
			return true;
	}
	return false;
}

/* ----------------------------------------------------------------
 *		ExecEvalAggref
 *
 *		Returns a Datum whose value is the value of the precomputed
 *		aggregate found in the given expression context.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalAggref(AggrefExprState *aggref, ExprContext *econtext,
			   bool *isNull, ExprDoneCond *isDone)
{
	if (isDone)
		*isDone = ExprSingleResult;

	if (econtext->ecxt_aggvalues == NULL)		/* safety check */
		elog(ERROR, "no aggregates in this expression context");

	*isNull = econtext->ecxt_aggnulls[aggref->aggno];
	return econtext->ecxt_aggvalues[aggref->aggno];
}

/* ----------------------------------------------------------------
 *		ExecEvalWindowFunc
 *
 *		Returns a Datum whose value is the value of the precomputed
 *		window function found in the given expression context.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalWindowFunc(WindowFuncExprState *wfunc, ExprContext *econtext,
				   bool *isNull, ExprDoneCond *isDone)
{
	if (isDone)
		*isDone = ExprSingleResult;

	if (econtext->ecxt_aggvalues == NULL)		/* safety check */
		elog(ERROR, "no window functions in this expression context");

	*isNull = econtext->ecxt_aggnulls[wfunc->wfuncno];
	return econtext->ecxt_aggvalues[wfunc->wfuncno];
}

/* ----------------------------------------------------------------
 *		ExecEvalScalarVar
 *
 *		Returns a Datum whose value is the value of a scalar (not whole-row)
 *		range variable with respect to given expression context.
 *
 * Note: ExecEvalScalarVar is executed only the first time through in a given
 * plan; it changes the ExprState's function pointer to pass control directly
 * to ExecEvalScalarVarFast after making one-time checks.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalScalarVar(ExprState *exprstate, ExprContext *econtext,
				  bool *isNull, ExprDoneCond *isDone)
{
	Var		   *variable = (Var *) exprstate->expr;
	TupleTableSlot *slot;
	AttrNumber	attnum;

	if (isDone)
		*isDone = ExprSingleResult;

	/* Get the input slot and attribute number we want */
	switch (variable->varno)
	{
		case INNER_VAR: /* get the tuple from the inner node */
			slot = econtext->ecxt_innertuple;
			break;

		case OUTER_VAR: /* get the tuple from the outer node */
			slot = econtext->ecxt_outertuple;
			break;

			/* INDEX_VAR is handled by default case */

		default:				/* get the tuple from the relation being
								 * scanned */
			slot = econtext->ecxt_scantuple;
			break;
	}

	attnum = variable->varattno;

	/* This was checked by ExecInitExpr */
	Assert(attnum != InvalidAttrNumber);

	/*
	 * If it's a user attribute, check validity (bogus system attnums will be
	 * caught inside slot_getattr).  What we have to check for here is the
	 * possibility of an attribute having been changed in type since the plan
	 * tree was created.  Ideally the plan will get invalidated and not
	 * re-used, but just in case, we keep these defenses.  Fortunately it's
	 * sufficient to check once on the first time through.
	 *
	 * Note: we allow a reference to a dropped attribute.  slot_getattr will
	 * force a NULL result in such cases.
	 *
	 * Note: ideally we'd check typmod as well as typid, but that seems
	 * impractical at the moment: in many cases the tupdesc will have been
	 * generated by ExecTypeFromTL(), and that can't guarantee to generate an
	 * accurate typmod in all cases, because some expression node types don't
	 * carry typmod.
	 */
	if (attnum > 0)
	{
		TupleDesc	slot_tupdesc = slot->tts_tupleDescriptor;
		Form_pg_attribute attr;

		if (attnum > slot_tupdesc->natts)		/* should never happen */
			elog(ERROR, "attribute number %d exceeds number of columns %d",
				 attnum, slot_tupdesc->natts);

		attr = slot_tupdesc->attrs[attnum - 1];

		/* can't check type if dropped, since atttypid is probably 0 */
		if (!attr->attisdropped)
		{
			if (variable->vartype != attr->atttypid)
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("attribute %d has wrong type", attnum),
						 errdetail("Table has type %s, but query expects %s.",
								   format_type_be(attr->atttypid),
								   format_type_be(variable->vartype))));
		}
	}

	/* Skip the checking on future executions of node */
	exprstate->evalfunc = ExecEvalScalarVarFast;

	/* Fetch the value from the slot */
	return slot_getattr(slot, attnum, isNull);
}

/* ----------------------------------------------------------------
 *		ExecEvalScalarVarFast
 *
 *		Returns a Datum for a scalar variable.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalScalarVarFast(ExprState *exprstate, ExprContext *econtext,
					  bool *isNull, ExprDoneCond *isDone)
{
	Var		   *variable = (Var *) exprstate->expr;
	TupleTableSlot *slot;
	AttrNumber	attnum;

	if (isDone)
		*isDone = ExprSingleResult;

	/* Get the input slot and attribute number we want */
	switch (variable->varno)
	{
		case INNER_VAR: /* get the tuple from the inner node */
			slot = econtext->ecxt_innertuple;
			break;

		case OUTER_VAR: /* get the tuple from the outer node */
			slot = econtext->ecxt_outertuple;
			break;

			/* INDEX_VAR is handled by default case */

		default:				/* get the tuple from the relation being
								 * scanned */
			slot = econtext->ecxt_scantuple;
			break;
	}

	attnum = variable->varattno;

	/* Fetch the value from the slot */
	return slot_getattr(slot, attnum, isNull);
}

/* ----------------------------------------------------------------
 *		ExecEvalWholeRowVar
 *
 *		Returns a Datum whose value is the value of a whole-row range
 *		variable with respect to given expression context.
 *
 * Note: ExecEvalWholeRowVar is executed only the first time through in a
 * given plan; it changes the ExprState's function pointer to pass control
 * directly to ExecEvalWholeRowFast or ExecEvalWholeRowSlow after making
 * one-time checks.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalWholeRowVar(WholeRowVarExprState *wrvstate, ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone)
{
	Var		   *variable = (Var *) wrvstate->xprstate.expr;
	TupleTableSlot *slot;
	TupleDesc	slot_tupdesc;
	bool		needslow = false;

	if (isDone)
		*isDone = ExprSingleResult;

	/* This was checked by ExecInitExpr */
	Assert(variable->varattno == InvalidAttrNumber);

	/* Get the input slot we want */
	switch (variable->varno)
	{
		case INNER_VAR: /* get the tuple from the inner node */
			slot = econtext->ecxt_innertuple;
			break;

		case OUTER_VAR: /* get the tuple from the outer node */
			slot = econtext->ecxt_outertuple;
			break;

			/* INDEX_VAR is handled by default case */

		default:				/* get the tuple from the relation being
								 * scanned */
			slot = econtext->ecxt_scantuple;
			break;
	}

	/*
	 * If the input tuple came from a subquery, it might contain "resjunk"
	 * columns (such as GROUP BY or ORDER BY columns), which we don't want to
	 * keep in the whole-row result.  We can get rid of such columns by
	 * passing the tuple through a JunkFilter --- but to make one, we have to
	 * lay our hands on the subquery's targetlist.  Fortunately, there are not
	 * very many cases where this can happen, and we can identify all of them
	 * by examining our parent PlanState.  We assume this is not an issue in
	 * standalone expressions that don't have parent plans.  (Whole-row Vars
	 * can occur in such expressions, but they will always be referencing
	 * table rows.)
	 */
	if (wrvstate->parent)
	{
		PlanState  *subplan = NULL;

		switch (nodeTag(wrvstate->parent))
		{
			case T_SubqueryScanState:
				subplan = ((SubqueryScanState *) wrvstate->parent)->subplan;
				break;
			case T_CteScanState:
				subplan = ((CteScanState *) wrvstate->parent)->cteplanstate;
				break;
			default:
				break;
		}

		if (subplan)
		{
			bool		junk_filter_needed = false;
			ListCell   *tlist;

			/* Detect whether subplan tlist actually has any junk columns */
			foreach(tlist, subplan->plan->targetlist)
			{
				TargetEntry *tle = (TargetEntry *) lfirst(tlist);

				if (tle->resjunk)
				{
					junk_filter_needed = true;
					break;
				}
			}

			/* If so, build the junkfilter in the query memory context */
			if (junk_filter_needed)
			{
				MemoryContext oldcontext;

				oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
				wrvstate->wrv_junkFilter =
					ExecInitJunkFilter(subplan->plan->targetlist,
									   ExecGetResultType(subplan)->tdhasoid,
							ExecInitExtraTupleSlot(wrvstate->parent->state));
				MemoryContextSwitchTo(oldcontext);
			}
		}
	}

	/* Apply the junkfilter if any */
	if (wrvstate->wrv_junkFilter != NULL)
		slot = ExecFilterJunk(wrvstate->wrv_junkFilter, slot);

	slot_tupdesc = slot->tts_tupleDescriptor;

	/*
	 * If it's a RECORD Var, we'll use the slot's type ID info.  It's likely
	 * that the slot's type is also RECORD; if so, make sure it's been
	 * "blessed", so that the Datum can be interpreted later.
	 *
	 * If the Var identifies a named composite type, we must check that the
	 * actual tuple type is compatible with it.
	 */
	if (variable->vartype == RECORDOID)
	{
		if (slot_tupdesc->tdtypeid == RECORDOID &&
			slot_tupdesc->tdtypmod < 0)
			assign_record_type_typmod(slot_tupdesc);
	}
	else
	{
		TupleDesc	var_tupdesc;
		int			i;

		/*
		 * We really only care about numbers of attributes and data types.
		 * Also, we can ignore type mismatch on columns that are dropped in
		 * the destination type, so long as (1) the physical storage matches
		 * or (2) the actual column value is NULL.	Case (1) is helpful in
		 * some cases involving out-of-date cached plans, while case (2) is
		 * expected behavior in situations such as an INSERT into a table with
		 * dropped columns (the planner typically generates an INT4 NULL
		 * regardless of the dropped column type).	If we find a dropped
		 * column and cannot verify that case (1) holds, we have to use
		 * ExecEvalWholeRowSlow to check (2) for each row.
		 */
		var_tupdesc = lookup_rowtype_tupdesc(variable->vartype, -1);

		if (var_tupdesc->natts != slot_tupdesc->natts)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("table row type and query-specified row type do not match"),
					 errdetail_plural("Table row contains %d attribute, but query expects %d.",
				   "Table row contains %d attributes, but query expects %d.",
									  slot_tupdesc->natts,
									  slot_tupdesc->natts,
									  var_tupdesc->natts)));

		for (i = 0; i < var_tupdesc->natts; i++)
		{
			Form_pg_attribute vattr = var_tupdesc->attrs[i];
			Form_pg_attribute sattr = slot_tupdesc->attrs[i];

			if (vattr->atttypid == sattr->atttypid)
				continue;		/* no worries */
			if (!vattr->attisdropped)
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("table row type and query-specified row type do not match"),
						 errdetail("Table has type %s at ordinal position %d, but query expects %s.",
								   format_type_be(sattr->atttypid),
								   i + 1,
								   format_type_be(vattr->atttypid))));

			if (vattr->attlen != sattr->attlen ||
				vattr->attalign != sattr->attalign)
				needslow = true;	/* need runtime check for null */
		}

		ReleaseTupleDesc(var_tupdesc);
	}

	/* Skip the checking on future executions of node */
	if (needslow)
		wrvstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalWholeRowSlow;
	else
		wrvstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalWholeRowFast;

	/* Fetch the value */
	return (*wrvstate->xprstate.evalfunc) ((ExprState *) wrvstate, econtext,
										   isNull, isDone);
}

/* ----------------------------------------------------------------
 *		ExecEvalWholeRowFast
 *
 *		Returns a Datum for a whole-row variable.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalWholeRowFast(WholeRowVarExprState *wrvstate, ExprContext *econtext,
					 bool *isNull, ExprDoneCond *isDone)
{
	Var		   *variable = (Var *) wrvstate->xprstate.expr;
	TupleTableSlot *slot;
	HeapTuple	tuple;
	TupleDesc	tupleDesc;
	HeapTupleHeader dtuple;

	if (isDone)
		*isDone = ExprSingleResult;
	*isNull = false;

	/* Get the input slot we want */
	switch (variable->varno)
	{
		case INNER_VAR: /* get the tuple from the inner node */
			slot = econtext->ecxt_innertuple;
			break;

		case OUTER_VAR: /* get the tuple from the outer node */
			slot = econtext->ecxt_outertuple;
			break;

			/* INDEX_VAR is handled by default case */

		default:				/* get the tuple from the relation being
								 * scanned */
			slot = econtext->ecxt_scantuple;
			break;
	}

	/* Apply the junkfilter if any */
	if (wrvstate->wrv_junkFilter != NULL)
		slot = ExecFilterJunk(wrvstate->wrv_junkFilter, slot);

	tuple = ExecFetchSlotTuple(slot);
	tupleDesc = slot->tts_tupleDescriptor;

	/*
	 * We have to make a copy of the tuple so we can safely insert the Datum
	 * overhead fields, which are not set in on-disk tuples.
	 */
	dtuple = (HeapTupleHeader) palloc(tuple->t_len);
	memcpy((char *) dtuple, (char *) tuple->t_data, tuple->t_len);

	HeapTupleHeaderSetDatumLength(dtuple, tuple->t_len);

	/*
	 * If the Var identifies a named composite type, label the tuple with that
	 * type; otherwise use what is in the tupleDesc.
	 */
	if (variable->vartype != RECORDOID)
	{
		HeapTupleHeaderSetTypeId(dtuple, variable->vartype);
		HeapTupleHeaderSetTypMod(dtuple, variable->vartypmod);
	}
	else
	{
		HeapTupleHeaderSetTypeId(dtuple, tupleDesc->tdtypeid);
		HeapTupleHeaderSetTypMod(dtuple, tupleDesc->tdtypmod);
	}

	return PointerGetDatum(dtuple);
}

/* ----------------------------------------------------------------
 *		ExecEvalWholeRowSlow
 *
 *		Returns a Datum for a whole-row variable, in the "slow" case where
 *		we can't just copy the subplan's output.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalWholeRowSlow(WholeRowVarExprState *wrvstate, ExprContext *econtext,
					 bool *isNull, ExprDoneCond *isDone)
{
	Var		   *variable = (Var *) wrvstate->xprstate.expr;
	TupleTableSlot *slot;
	HeapTuple	tuple;
	TupleDesc	tupleDesc;
	TupleDesc	var_tupdesc;
	HeapTupleHeader dtuple;
	int			i;

	if (isDone)
		*isDone = ExprSingleResult;
	*isNull = false;

	/* Get the input slot we want */
	switch (variable->varno)
	{
		case INNER_VAR: /* get the tuple from the inner node */
			slot = econtext->ecxt_innertuple;
			break;

		case OUTER_VAR: /* get the tuple from the outer node */
			slot = econtext->ecxt_outertuple;
			break;

			/* INDEX_VAR is handled by default case */

		default:				/* get the tuple from the relation being
								 * scanned */
			slot = econtext->ecxt_scantuple;
			break;
	}

	/* Apply the junkfilter if any */
	if (wrvstate->wrv_junkFilter != NULL)
		slot = ExecFilterJunk(wrvstate->wrv_junkFilter, slot);

	tuple = ExecFetchSlotTuple(slot);
	tupleDesc = slot->tts_tupleDescriptor;

	Assert(variable->vartype != RECORDOID);
	var_tupdesc = lookup_rowtype_tupdesc(variable->vartype, -1);

	/* Check to see if any dropped attributes are non-null */
	for (i = 0; i < var_tupdesc->natts; i++)
	{
		Form_pg_attribute vattr = var_tupdesc->attrs[i];
		Form_pg_attribute sattr = tupleDesc->attrs[i];

		if (!vattr->attisdropped)
			continue;			/* already checked non-dropped cols */
		if (heap_attisnull(tuple, i + 1))
			continue;			/* null is always okay */
		if (vattr->attlen != sattr->attlen ||
			vattr->attalign != sattr->attalign)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("table row type and query-specified row type do not match"),
					 errdetail("Physical storage mismatch on dropped attribute at ordinal position %d.",
							   i + 1)));
	}

	/*
	 * We have to make a copy of the tuple so we can safely insert the Datum
	 * overhead fields, which are not set in on-disk tuples.
	 */
	dtuple = (HeapTupleHeader) palloc(tuple->t_len);
	memcpy((char *) dtuple, (char *) tuple->t_data, tuple->t_len);

	HeapTupleHeaderSetDatumLength(dtuple, tuple->t_len);
	HeapTupleHeaderSetTypeId(dtuple, variable->vartype);
	HeapTupleHeaderSetTypMod(dtuple, variable->vartypmod);

	ReleaseTupleDesc(var_tupdesc);

	return PointerGetDatum(dtuple);
}

/* ----------------------------------------------------------------
 *		ExecEvalConst
 *
 *		Returns the value of a constant.
 *
 *		Note that for pass-by-ref datatypes, we return a pointer to the
 *		actual constant node.  This is one of the reasons why functions
 *		must treat their input arguments as read-only.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalConst(ExprState *exprstate, ExprContext *econtext,
			  bool *isNull, ExprDoneCond *isDone)
{
	Const	   *con = (Const *) exprstate->expr;

	if (isDone)
		*isDone = ExprSingleResult;

	*isNull = con->constisnull;
	return con->constvalue;
}

/* ----------------------------------------------------------------
 *		ExecEvalParamExec
 *
 *		Returns the value of a PARAM_EXEC parameter.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalParamExec(ExprState *exprstate, ExprContext *econtext,
				  bool *isNull, ExprDoneCond *isDone)
{
	Param	   *expression = (Param *) exprstate->expr;
	int			thisParamId = expression->paramid;
	ParamExecData *prm;

	if (isDone)
		*isDone = ExprSingleResult;

	/*
	 * PARAM_EXEC params (internal executor parameters) are stored in the
	 * ecxt_param_exec_vals array, and can be accessed by array index.
	 */
	prm = &(econtext->ecxt_param_exec_vals[thisParamId]);
	if (prm->execPlan != NULL)
	{
		/* Parameter not evaluated yet, so go do it */
		ExecSetParamPlan(prm->execPlan, econtext);
		/* ExecSetParamPlan should have processed this param... */
		Assert(prm->execPlan == NULL);
	}
	*isNull = prm->isnull;
	return prm->value;
}

/* ----------------------------------------------------------------
 *		ExecEvalParamExtern
 *
 *		Returns the value of a PARAM_EXTERN parameter.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalParamExtern(ExprState *exprstate, ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone)
{
	Param	   *expression = (Param *) exprstate->expr;
	int			thisParamId = expression->paramid;
	ParamListInfo paramInfo = econtext->ecxt_param_list_info;

	if (isDone)
		*isDone = ExprSingleResult;

	/*
	 * PARAM_EXTERN parameters must be sought in ecxt_param_list_info.
	 */
	if (paramInfo &&
		thisParamId > 0 && thisParamId <= paramInfo->numParams)
	{
		ParamExternData *prm = &paramInfo->params[thisParamId - 1];

		/* give hook a chance in case parameter is dynamic */
		if (!OidIsValid(prm->ptype) && paramInfo->paramFetch != NULL)
			(*paramInfo->paramFetch) (paramInfo, thisParamId);

		if (OidIsValid(prm->ptype))
		{
			/* safety check in case hook did something unexpected */
			if (prm->ptype != expression->paramtype)
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("type of parameter %d (%s) does not match that when preparing the plan (%s)",
								thisParamId,
								format_type_be(prm->ptype),
								format_type_be(expression->paramtype))));

			*isNull = prm->isnull;
			return prm->value;
		}
	}

	ereport(ERROR,
			(errcode(ERRCODE_UNDEFINED_OBJECT),
			 errmsg("no value found for parameter %d", thisParamId)));
	return (Datum) 0;			/* keep compiler quiet */
}


/* ----------------------------------------------------------------
 *		ExecEvalOper / ExecEvalFunc support routines
 * ----------------------------------------------------------------
 */

/*
 *		GetAttributeByName
 *		GetAttributeByNum
 *
 *		These functions return the value of the requested attribute
 *		out of the given tuple Datum.
 *		C functions which take a tuple as an argument are expected
 *		to use these.  Ex: overpaid(EMP) might call GetAttributeByNum().
 *		Note: these are actually rather slow because they do a typcache
 *		lookup on each call.
 */
Datum
GetAttributeByNum(HeapTupleHeader tuple,
				  AttrNumber attrno,
				  bool *isNull)
{
	Datum		result;
	Oid			tupType;
	int32		tupTypmod;
	TupleDesc	tupDesc;
	HeapTupleData tmptup;

	if (!AttributeNumberIsValid(attrno))
		elog(ERROR, "invalid attribute number %d", attrno);

	if (isNull == NULL)
		elog(ERROR, "a NULL isNull pointer was passed");

	if (tuple == NULL)
	{
		/* Kinda bogus but compatible with old behavior... */
		*isNull = true;
		return (Datum) 0;
	}

	tupType = HeapTupleHeaderGetTypeId(tuple);
	tupTypmod = HeapTupleHeaderGetTypMod(tuple);
	tupDesc = lookup_rowtype_tupdesc(tupType, tupTypmod);

	/*
	 * heap_getattr needs a HeapTuple not a bare HeapTupleHeader.  We set all
	 * the fields in the struct just in case user tries to inspect system
	 * columns.
	 */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
	ItemPointerSetInvalid(&(tmptup.t_self));
	tmptup.t_tableOid = InvalidOid;
	tmptup.t_data = tuple;

	result = heap_getattr(&tmptup,
						  attrno,
						  tupDesc,
						  isNull);

	ReleaseTupleDesc(tupDesc);

	return result;
}

Datum
GetAttributeByName(HeapTupleHeader tuple, const char *attname, bool *isNull)
{
	AttrNumber	attrno;
	Datum		result;
	Oid			tupType;
	int32		tupTypmod;
	TupleDesc	tupDesc;
	HeapTupleData tmptup;
	int			i;

	if (attname == NULL)
		elog(ERROR, "invalid attribute name");

	if (isNull == NULL)
		elog(ERROR, "a NULL isNull pointer was passed");

	if (tuple == NULL)
	{
		/* Kinda bogus but compatible with old behavior... */
		*isNull = true;
		return (Datum) 0;
	}

	tupType = HeapTupleHeaderGetTypeId(tuple);
	tupTypmod = HeapTupleHeaderGetTypMod(tuple);
	tupDesc = lookup_rowtype_tupdesc(tupType, tupTypmod);

	attrno = InvalidAttrNumber;
	for (i = 0; i < tupDesc->natts; i++)
	{
		if (namestrcmp(&(tupDesc->attrs[i]->attname), attname) == 0)
		{
			attrno = tupDesc->attrs[i]->attnum;
			break;
		}
	}

	if (attrno == InvalidAttrNumber)
		elog(ERROR, "attribute \"%s\" does not exist", attname);

	/*
	 * heap_getattr needs a HeapTuple not a bare HeapTupleHeader.  We set all
	 * the fields in the struct just in case user tries to inspect system
	 * columns.
	 */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
	ItemPointerSetInvalid(&(tmptup.t_self));
	tmptup.t_tableOid = InvalidOid;
	tmptup.t_data = tuple;

	result = heap_getattr(&tmptup,
						  attrno,
						  tupDesc,
						  isNull);

	ReleaseTupleDesc(tupDesc);

	return result;
}

/*
 * func_expr_errcontext
 *
 * When calling ereport, this can be used to add some information about the
 * expression node which encountered the error.
 *
 * If showInternalNames is true, the (internal or C-language external)
 * function's entry point name and library name are displayed; this can help
 * to diagnose errors caused by incorrect use of the C-language API or by
 * cataloging with incorrect DDL.  Also, for all languages, when the function
 * is invoked as an operator, not only the operator symbol is shown but also
 * the procedure name.
 */
int
func_expr_errcontext(Expr *expr, bool showInternalNames)
{
	if (!expr)
		return 0;

	switch (expr->type)
	{
		/*
		 * Parse tree nodes
		 */
		case T_FuncExpr:
			{
				FuncExpr   *funcExpr = (FuncExpr *) expr;

				if (showInternalNames)
					fmgr_func_errcontext(funcExpr->funcid, true);
				else if (funcExpr->funcid != InvalidOid)
					errcontext("Function \"%s\"", format_procedure(funcExpr->funcid));
				break;
			}
		case T_OpExpr:
			{
				OpExpr	   *opExpr = (OpExpr *) expr;

				if (showInternalNames)
					fmgr_func_errcontext(opExpr->opfuncid, true);
				if (opExpr->opno != InvalidOid)
					errcontext("Operator \"%s\"", format_operator(opExpr->opno));
				break;
			}
		case T_DistinctExpr:
			{
				DistinctExpr *distinctExpr = (DistinctExpr *) expr;

				if (showInternalNames)
					fmgr_func_errcontext(distinctExpr->opfuncid, true);
				if (distinctExpr->opno != InvalidOid)
					errcontext("\"IS DISTINCT FROM\" test using operator \"%s\"",
							   format_operator(distinctExpr->opno));
				break;
			}
		case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr *scalarArrayOpExpr = (ScalarArrayOpExpr *) expr;

				if (showInternalNames)
					fmgr_func_errcontext(scalarArrayOpExpr->opfuncid, true);
				if (scalarArrayOpExpr->opno != InvalidOid)
					errcontext("\"%s\" array comparison using operator \"%s\"",
							   scalarArrayOpExpr->useOr ? "ANY" : "ALL",
							   format_operator(scalarArrayOpExpr->opno));
				break;
			}
		case T_NullIfExpr:
			{
				NullIfExpr *nullIfExpr = (NullIfExpr *) expr;

				if (showInternalNames)
					fmgr_func_errcontext(nullIfExpr->opfuncid, true);
				if (nullIfExpr->opno != InvalidOid)
					errcontext("NULLIF test using operator \"%s\"",
							   format_operator(nullIfExpr->opno));
				break;
			}

		/*
		 * ExprState nodes
		 */
		case T_FuncExprState:
		case T_ScalarArrayOpExprState:
			return func_expr_errcontext(((ExprState *) expr)->expr, showInternalNames);

		default:
			break;
	}
	return 0;					/* return value does not matter */
}

/*
 * get_expr_result_tupdesc
 *
 * Build tuple descriptor that can be used for reading an expression result
 * from a tuplestore.
 */
void
get_expr_result_tupdesc(Expr *expr,
						const char *scalarattnameornull,
						TupleDesc *tupdesc_out,
						bool *returnstuple_out)
{
	TypeFuncClass functypclass;
	Oid			funcrettype;
	TupleDesc	tupdesc;
	bool		returnstuple;

	Assert(tupdesc_out != NULL &&
		   returnstuple_out != NULL);

	/*
	 * Get function result data type.  If it is a row type, get its TupleDesc.
	 */
	functypclass = get_expr_result_type((Node *) expr, &funcrettype, &tupdesc);

	/*
	 * We have a tuple descriptor if and only if the function returns either a
	 * cataloged row type, or a RECORD type whose field types have been
	 * determined.  The descriptor has been palloc'ed in the current memory
	 * context, and isn't refcounted, so caller need not ReleaseTupleDesc().
	 */
	Assert(tupdesc ? (functypclass == TYPEFUNC_COMPOSITE &&
					  tupdesc->tdrefcount == -1 &&
					  GetMemoryChunkContext(tupdesc) == CurrentMemoryContext)
		   : (functypclass != TYPEFUNC_COMPOSITE));

	/* Composite data type, e.g. a table's row type */
	if (functypclass == TYPEFUNC_COMPOSITE)
		returnstuple = true;

	/* Base data type, i.e. scalar */
	else if (functypclass == TYPEFUNC_SCALAR)
	{
		tupdesc = CreateTemplateTupleDesc(1, false);
		TupleDescInitEntry(tupdesc,
						   (AttrNumber) 1,
						   scalarattnameornull,
						   funcrettype,
						   -1,
						   0);
		TupleDescInitEntryCollation(tupdesc,
									(AttrNumber) 1,
									exprCollation((Node *) expr));
		returnstuple = false;
	}

	/* Function will dynamically determine its result tuple format. */
	else if (functypclass == TYPEFUNC_RECORD)
	{
		/* This will work if function doesn't need an expectedDesc */
		returnstuple = true;
	}

	/* Pseudotype.	Fails later on if function needs an expectedDesc. */
	else
		returnstuple = false;

	*tupdesc_out = tupdesc;
	*returnstuple_out = returnstuple;
}

/*
 * callback function in case a FuncExpr returning a set needs to be shut down
 * before it has been run to completion
 *
 * Note that ExprContext callbacks are invoked in LIFO order; so by the
 * time this callback is invoked, any callbacks which were registered by
 * the function itself have already been executed.
 */
static void
ShutdownFuncExpr(Datum arg)
{
	FuncExprState *fcache = (FuncExprState *) DatumGetPointer(arg);
	ReturnSetInfo *rsinfo = &fcache->rsinfo;

	/* If we have a slot, make sure it's let go of any tuplestore pointer */
	if (fcache->dematerializeSlot)
		ExecClearTuple(fcache->dematerializeSlot);

	/* Release any open tuplestore */
	if (rsinfo->setResult)
		tuplestore_end(rsinfo->setResult);
	rsinfo->setResult = NULL;

	/*
	 * If the function was expecting to be called again to return more output,
	 * discard its saved state to be ready for a fresh start.  (To keep this
	 * from happening, the function can register its own ExprContext callback,
	 * in which it should clean up and set rsinfo->isDone = ExprSingleResult.)
	 */
	if (rsinfo->isDone == ExprMultipleResult)
		fcache->func.fn_extra = NULL;

	/* Clear any active set-argument state */
	fcache->argIsDone = ExprEndResult;
	rsinfo->isDone = ExprSingleResult;

	/* Free any pass-by-reference outputs and garbage left by arg evaluation. */
	if (fcache->argEvalContext)
		MemoryContextReset(fcache->argEvalContext);

	/* execUtils will deregister the callback... */
	fcache->shutdown_reg = false;
}

/*
 * get_cached_rowtype: utility function to lookup a rowtype tupdesc
 *
 * type_id, typmod: identity of the rowtype
 * cache_field: where to cache the TupleDesc pointer in expression state node
 *		(field must be initialized to NULL)
 * econtext: expression context we are executing in
 *
 * NOTE: because the shutdown callback will be called during plan rescan,
 * must be prepared to re-do this during any node execution; cannot call
 * just once during expression initialization
 */
static TupleDesc
get_cached_rowtype(Oid type_id, int32 typmod,
				   TupleDesc *cache_field, ExprContext *econtext)
{
	TupleDesc	tupDesc = *cache_field;

	/* Do lookup if no cached value or if requested type changed */
	if (tupDesc == NULL ||
		type_id != tupDesc->tdtypeid ||
		typmod != tupDesc->tdtypmod)
	{
		tupDesc = lookup_rowtype_tupdesc(type_id, typmod);

		if (*cache_field)
		{
			/* Release old tupdesc; but callback is already registered */
			ReleaseTupleDesc(*cache_field);
		}
		else
		{
			/* Need to register shutdown callback to release tupdesc */
			RegisterExprContextCallback(econtext,
										ShutdownTupleDescRef,
										PointerGetDatum(cache_field));
		}
		*cache_field = tupDesc;
	}
	return tupDesc;
}

/*
 * Callback function to release a tupdesc refcount at expression tree shutdown
 */
static void
ShutdownTupleDescRef(Datum arg)
{
	TupleDesc  *cache_field = (TupleDesc *) DatumGetPointer(arg);

	if (*cache_field)
		ReleaseTupleDesc(*cache_field);
	*cache_field = NULL;
}

/*
 *	   tupledesc_match
 *
 * Check that function result tuple type (src_tupdesc) matches or can
 * be considered to match what the query expects (dst_tupdesc). If
 * they don't match, ereport.
 *
 * We really only care about number of attributes and data type.
 * Also, we can ignore type mismatch on columns that are dropped in the
 * destination type, so long as the physical storage matches.  This is
 * helpful in some cases involving out-of-date cached plans.
 *
 * If 'expr' is non-null, it's used to add error message context information.
 */
static void
tupledesc_match(Expr *expr, TupleDesc dst_tupdesc, TupleDesc src_tupdesc)
{
	int			i;

	if (dst_tupdesc->natts != src_tupdesc->natts)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("function return row and query-specified return row do not match"),
				 errdetail_plural("Returned row contains %d attribute, but query expects %d.",
								  "Returned row contains %d attributes, but query expects %d.",
								  src_tupdesc->natts,
								  src_tupdesc->natts, dst_tupdesc->natts),
				 func_expr_errcontext(expr, false)));

	for (i = 0; i < dst_tupdesc->natts; i++)
	{
		Form_pg_attribute dattr = dst_tupdesc->attrs[i];
		Form_pg_attribute sattr = src_tupdesc->attrs[i];

		if (sattr->atttypid == dattr->atttypid)
			continue;
		if (IsBinaryCoercible(sattr->atttypid, dattr->atttypid))
			continue;			/* no worries */
		if (!dattr->attisdropped)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("function return row and query-specified return row do not match"),
					 errdetail("Returned type %s at ordinal position %d, but query expects %s.",
							   format_type_be(sattr->atttypid),
							   i + 1,
							   format_type_be(dattr->atttypid)),
					 func_expr_errcontext(expr, false)));

		if (dattr->attlen != sattr->attlen ||
			dattr->attalign != sattr->attalign)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("function return row and query-specified return row do not match"),
					 errdetail("Physical storage mismatch on dropped attribute at ordinal position %d.",
							   i + 1),
					 func_expr_errcontext(expr, false)));
	}
}

/*
 *		ExecVerifyExpectedTupleDesc
 *
 * This routine raises an error if the tuple descriptor 'actualDesc'
 * specifies a format that is not binary compatible with the expected result
 * tuple descriptor (fcinfo->rsinfo->expectedDesc) for the function call.
 *
 * If no expected tuple descriptor is available, this routine stores a copy
 * of the actualDesc into the expected descriptor field, where it will remain
 * for the duration of the query.
 *
 * (For set-returning functions using materialize mode, the expectedDesc will
 * be used to read the results from the tuplestore.  For functions not
 * returning sets or not using materialize mode, the expectedDesc isn't used
 * for anything other than this sanity check.)
 */
void
ExecVerifyExpectedTupleDesc(FunctionCallInfo fcinfo, TupleDesc actualDesc)
{
	ReturnSetInfo *rsinfo = (ReturnSetInfo *) fcinfo->resultinfo;
	MemoryContext oldcxt;

	Assert(rsinfo && IsA(rsinfo, ReturnSetInfo));
	Assert(actualDesc != NULL);

	/* Verify the actual result tuple format matches the expected layout. */
	if (rsinfo->expectedDesc)
		tupledesc_match((Expr *) fcinfo->flinfo->fn_expr, rsinfo->expectedDesc,
						actualDesc);

	/* If no expectedDesc, save the actualDesc. */
	else
	{
		oldcxt =
			MemoryContextSwitchTo(rsinfo->econtext->ecxt_per_query_memory);
		rsinfo->expectedDesc = CreateTupleDescCopy(actualDesc);
		MemoryContextSwitchTo(oldcxt);
	}
}

/*
 *		ExecVerifyReturnedRowType
 *
 * This routine is used after evaluating an expression that returns a non-null
 * result of a row type: either a composite type defined in the catalog, or a
 * RECORD type defined transiently at runtime.	The result could come from a
 * general set-valued or non-set-valued expression, or from a set-returning
 * function that has chosen value-per-call mode.
 *
 * This routine raises an error if the actual row type isn't binary compatible
 * with 'expectedDesc', the format expected by the consumer of the result.  If
 * expectedDesc is NULL, this routine raises an error if the actual row type
 * changes incompatibly from one call to the next.
 *
 * If 'expr' is non-null, it's used to add error message context information.
 *
 * If a non-toasted 'result' was given, it is returned unchanged.  Otherwise a
 * detoasted copy of the 'result' tuple, palloc'ed in the current memory
 * context, is returned, with hope that it needn't be re-detoasted later.
 */
Datum
ExecVerifyReturnedRowType(Expr *expr, Datum result, TupleDesc expectedDesc,
						  Oid *returnedTypeId_inout,
						  int32 *returnedTypMod_inout)
{
	HeapTupleHeader tuple;
	Oid				typid;
	int32			typmod;
	TupleDesc		actualtupdesc;

	/* Assume ok if "blessed" dynamic record type id is same as expected. */
	if (*returnedTypeId_inout == InvalidOid &&
		expectedDesc &&
		expectedDesc->tdtypeid == RECORDOID &&
		expectedDesc->tdtypmod != -1)
	{
		*returnedTypeId_inout = expectedDesc->tdtypeid;
		*returnedTypMod_inout = expectedDesc->tdtypmod;
	}
	
	/*
	 * Error if function returned (Datum) 0 but neglected to set proper flags.
	 * To return a null row (an abbreviation for a row with all columns null),
	 * non-set-returning functions must assign fcinfo->isnull = true; the same
	 * goes for set-returning functions in value-per-call mode.  Or, to return 
	 * an empty set (or end-of-set) in value-per-call protocol, the SRF should 
	 * have assigned rsinfo->isDone = ExprEndResult.  Or, to return an empty 
	 * or nonempty result set using Materialize Mode protocol, the SRF should 
	 * have assigned rsinfo->returnMode = SFRM_Materialize.
	 */
	if (DatumGetPointer(result) == NULL)
		ereport(ERROR,
			(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
			 errmsg("function return protocol was not followed"),
			 errhint("function returned void datum without proper flags"),
			 func_expr_errcontext(expr, true)));	

	/* Get row type and subtype from result tuple header. */
	tuple = DatumGetHeapTupleHeader(result);		/* (detoasts the tuple) */
	typid = HeapTupleHeaderGetTypeId(tuple);
	typmod = HeapTupleHeaderGetTypMod(tuple);

	/* Quick exit if the type and subtype were already found valid. */
	if (*returnedTypeId_inout == typid &&
		*returnedTypMod_inout == typmod &&
		*returnedTypeId_inout != InvalidOid)
		return PointerGetDatum(tuple);

	/* Look up the actual result tuple descriptor. */
	actualtupdesc = lookup_rowtype_tupdesc_noerror(typid, typmod, true);
	if (!actualtupdesc)
	{
		if (typid == RECORDOID && typmod == -1)
			ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg_internal("Function returned a row with incorrect format"),
				 errdetail("C function should call BlessTupleDesc before building tuple"),
				 func_expr_errcontext(expr, true)));
		else
			ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg_internal("Function returned a row with incorrect format"),
				 errdetail("Returned tuple header does not specify a valid "
						   "row type id (%u) and typmod (%d)",
						   (unsigned) typid, (int) typmod),
				 func_expr_errcontext(expr, true)));
	}

	/* Verify the actual result tuple format resembles the expected layout. */
	if (expectedDesc)
		tupledesc_match(expr, expectedDesc, actualtupdesc);

	/* Verify this tuple's format is similar to the previous one. */
	else if (*returnedTypeId_inout != InvalidOid)
	{
		expectedDesc = lookup_rowtype_tupdesc(*returnedTypeId_inout,
											  *returnedTypMod_inout);
		tupledesc_match(expr, expectedDesc, actualtupdesc);
		ReleaseTupleDesc(expectedDesc);
	}

 	ReleaseTupleDesc(actualtupdesc);

	/* Remember we have checked this type and subtype. */
	*returnedTypeId_inout = typid;
	*returnedTypMod_inout = typmod;
	return PointerGetDatum(tuple);
}


/*
 *		ExecInitTableFunction
 *
 * Prepares an expression tree to be executed.	Builds and returns an
 * ExprState tree paralleling the given Expr node tree. The ExprState tree
 * can then be handed to either ExecEvalExpr or ExecMaterializeTableFunction
 * for execution.
 *
 * This routine differs from ExecInitExpr in allowing the caller to specify
 * some extra information that may be applicable in case (a) the results of
 * the expression are to be collected into a tuplestore, and/or (b) the top
 * expression node invokes a procedure whose incomplete result type (RECORD
 * or SETOF RECORD) is to be augmented with specific type information given
 * explicitly by the caller.
 *
 * In case (a), an efficiency can be realized if the top expression node
 * invokes a set-returning function that uses "materialize mode" to return
 * its results in a tuplestore.  The tuplestore created by the function can
 * be captured by ExecMaterializeTableFunction() and processed directly by
 * the caller.	The set-returning function has to create the tuplestore with
 * suitable options determined by the caller's 'randomAccess' flag; to do so,
 * the function can use the init_materialize_mode() convenience routine.
 *
 * In case (b), the caller creates a tuple descriptor ('expectedDesc')
 * specifying the expected format of the result tuples.  The called function
 * is required to produce tuples that conform to this format.  If the caller
 * does not specify an expected tuple descriptor, then the called function may
 * produce tuples in any valid format, for which - if using materialize mode -
 * it must provide a descriptor by calling srf_verify_expected_tupdesc() or by
 * filling in the rsinfo->setDesc field.
 */
ExprState *
ExecInitTableFunction(Expr *expr,
					  PlanState *parent,
					  ExprContext *econtext,
					  TupleDesc expectedDesc,
					  bool returnsTuple,
					  bool randomAccess)
{
	ExprState  *state;

	/*
	 * Convert the expression to an ExprState tree.
	 */
	state = ExecInitExpr(expr, parent);

	/*
	 * If top node is a function call, do a little special initialization of
	 * the FuncExprState.
	 */
	if (IsA(state, FuncExprState))
	{
		FuncExprState *fcache = (FuncExprState *) state;
		Expr *expr = fcache->xprstate.expr;
		ReturnSetInfo *rsinfo = &fcache->rsinfo;

		/* Look up the function entry point and check permissions. */
		if (IsA(expr, FuncExpr))
		{
			FuncExpr *func = (FuncExpr *) fcache->xprstate.expr;

			init_fcache(func->funcid, func->inputcollid, fcache, econtext);
		}
		else if (IsA(expr, OpExpr))
		{
			OpExpr *op = (OpExpr *) expr;

			init_fcache(op->opfuncid, op->inputcollid, fcache, econtext);
		}
		else
			elog(ERROR, "unexpected node type: %d",  (int) nodeTag(expr));

		/* Install the expected result descriptor. */
		rsinfo->expectedDesc = expectedDesc;
		fcache->funcReturnsTuple = returnsTuple;

		/* Is it a set-returning function? */
		if (fcache->func.fn_retset)
		{
			/* Initialize SRF protocol flags. */
			rsinfo->allowedModes = SFRM_ValuePerCall | SFRM_Materialize;

			/* Tuplestore options required for use of materialize mode */
			if (randomAccess)
				rsinfo->allowedModes |= SFRM_Materialize_Random;

			/*
			 * If we happen to know that the function results will be consumed
			 * non-interactively - for example, if the results will be sorted
			 * before any output is sent to the client - then we could set
			 * the SFRM_Materialize_Preferred flag as a hint to inform the
			 * function that it might as well return all of its results at
			 * once in a tuplestore rather than taking extra trouble to give
			 * early results incrementally.  (On the other hand, feeding a
			 * sort with value-per-call mode would use less memory and less
			 * copying than materialize mode.)  Unfortunately at present we
			 * aren't informed what happens downstream of the FunctionScan;
			 * and we can't judge when materialize mode costs more than it
			 * saves.  So we never set the flag.  (The flag was originally
			 * intended to be set whenever the caller wanted to save results
			 * in a tuplestore, which formerly implied non-interactivity and
			 * negated the time-to-first-output benefit of value-per-call
			 * mode.  Nowadays FunctionScan passes results onward promptly
			 * after each call to the function, and functions can use
			 * materialize mode incrementally.)
			 */
		}
	}
	return state;
}

/*
 *		ExecMaterializeTableFunction
 *
 * Evaluate an expression and obtain the result as a stream of tuples which
 * are recorded in a tuplestore.
 *
 * On each call, this routine obtains the next result tuple and, if possible,
 * additional subsequent tuples, and returns true; or returns false if the
 * expression yields no more result tuples for the current inputs.
 *
 * On success, this routine returns true and places the first of the newly
 * acquired result tuples in 'slot'.  That tuple also exists in the tuplestore
 * preceding the current read position.  Zero or more subsequent tuples might
 * be available in the tuplestore after the current read position; the caller
 * should read them from there, and upon reaching eof in the tuplestore, call
 * this routine again for more.
 *
 * After this routine returns false, the caller can supply new inputs (e.g.
 * advance a scan providing input to Var nodes in the expression) and call
 * again for new results.
 *
 * Generally scanstate->tuplestorestate == NULL initially, and the tuplestore
 * is created when needed, either by this routine or by a set-returning
 * function which is called by the top node of the expression tree and uses
 * materialize mode.  A tuplestore might be created whether or not any rows
 * are returned.  The caller must eventually free the tuplestore by calling
 * tuplestore_end().
 *
 * Before this routine is called , the expression tree should be initialized
 * by ExecInitTableFunction or ExecInitExpr.
 */
bool
ExecMaterializeTableFunction(FunctionScanState *scanstate,
							 ExprContext *econtext,
							 TupleTableSlot *slot)
{
	Tuplestorestate	*tuplestorestate = scanstate->tuplestorestate;
	Datum			result;
	bool			isNull;
	ExprDoneCond	isDone;

	/*
	 * Normally the passed expression will be a FuncExpr, since the grammar
	 * requires a function call at the top level of a table function
	 * reference.  If it's a set-returning function and it has chosen - or yet
	 * may choose - materialize mode, we hope it will put its results into a
	 * tuplestore that our caller can process directly.
	 */
	if (IsA(scanstate->funcexpr, FuncExprState) &&
		(((FuncExprState *) scanstate->funcexpr)->rsinfo.allowedModes & SFRM_Materialize) != 0)
	{
		FuncExprState	*fcache = (FuncExprState *) scanstate->funcexpr;
		ReturnSetInfo	*rsinfo = &fcache->rsinfo;

		/* init_fcache has initialized the FuncExprState. */
		Assert(fcache->func.fn_oid != InvalidOid &&
			   IsA(rsinfo, ReturnSetInfo));
		Assert(fcache->func.fn_retset);

		for (;;)
		{
			Tuplestorestate	*oldsecondtuplestore = NULL;
			bool			nudge = false;

			/*
			 * If value-per-call mode has not been ruled out, then the
			 * set-returning function hasn't been called yet, or has given
			 * back ExprEndResult status (empty result) on every call so far.
			 * Offer caller's tuplestore (if provided) for the function's
			 * optional use in case it chooses materialize mode.
			 */
			if (rsinfo->allowedModes & SFRM_ValuePerCall)
				rsinfo->setResult = tuplestorestate;

			/*
			 * Single-tuplestore case.	We have a tuplestore retained from the
			 * first time around.  Offer it to the function, which we hope
			 * will append its new result tuples to the ones already there.
			 */
			else if (rsinfo->setResult == NULL)
			{
				Assert(tuplestorestate);

				rsinfo->setResult = tuplestorestate;

				/*
				 * Nudge the read position of the tuplestore back out of eof,
				 * to a position after the last tuple but before eof.  (The
				 * randomAccess option isn't needed for this.)  In case the
				 * function appends new result tuples, they'll be placed after
				 * the read position, so our caller can read the added results
				 * without further repositioning.
				 */
				if (tuplestore_ateof(tuplestorestate))
				{
					tuplestore_advance(tuplestorestate, false); /* backward */
					Assert(!tuplestore_ateof(tuplestorestate));
					nudge = true;
				}
			}

			/*
			 * Double-tuplestore case.	Return the next tuple from the
			 * uncooperative function's tuplestore and save a copy in the
			 * caller's tuplestore.  Caller's reading position stays at eof.
			 * When caller reads from the tuplestore, it will encounter eof
			 * immediately and call us again for another tuple.
			 */
			else
			{
				Assert(tuplestorestate &&
					   rsinfo->setResult != tuplestorestate);

				if (tuplestore_gettupleslot(rsinfo->setResult, true, false, slot))
				{
					tuplestore_puttupleslot(tuplestorestate, slot);
					return true;
				}

				/*
				 * Function can continue appending to its same tuplestore, or
				 * create another new one - in which case we'll free this one
				 * below.  Until then, leave the contents undisturbed, in case
				 * the function wants to refer to them for some reason.  Step
				 * back off eof so any new tuples will be appended after the
				 * reading position.  We don't give the function a second
				 * chance to append to the caller's tuplestore.
				 */
				tuplestore_advance(rsinfo->setResult, false);	/* backward */
				Assert(!tuplestore_ateof(rsinfo->setResult));
				oldsecondtuplestore = rsinfo->setResult;
			}
		
			/*
			 * Call the set-returning function.  Use low-level call that
			 * bypasses the dematerializer, so that we can take control of the
			 * result tuplestore if the function uses materialize mode.
			 */
			result = ExecEvalFuncSRF(fcache, econtext, &isNull, &isDone);

			/* Don't expose caller's tuplestore to ShutdownFuncExpr. */
			if (rsinfo->setResult == tuplestorestate)
				rsinfo->setResult = NULL;

			/*
			 * Free uncooperative function's old tuplestore if the function
			 * created a new one instead of continuing to use its old one.
			 */
			else if (oldsecondtuplestore &&
					 rsinfo->setResult != oldsecondtuplestore)
				tuplestore_end(oldsecondtuplestore);
			
			/* Quit if empty set or end of set. */
			if (isDone == ExprEndResult)
			{
				/* Nudge caller's read position onto eof as it was before. */
				if (nudge)
					tuplestore_advance(tuplestorestate, true);
				ExecClearTuple(slot);
				return false;
			}

			/*
			 * If value-per-call mode has just been chosen, break out of the
			 * for (;;) loop and continue below.  On subsequent calls we'll
			 * go straight down there, bypassing the for (;;) loop.
			 */
			if (rsinfo->returnMode == SFRM_ValuePerCall)
			{
				/* If caller provided tuplestore, nudge it forward onto eof. */
				if (tuplestorestate)
				{
					tuplestore_advance(tuplestorestate, true);
					Assert(tuplestore_ateof(tuplestorestate));
				}

				/*
				 * It's ok for function to create tuplestore before deciding
				 * upon value-per-call mode.  If so, free it.  Assumed empty.
				 */
				if (rsinfo->setResult)
				{
					tuplestore_end(rsinfo->setResult);
					rsinfo->setResult = NULL;
				}
				break;
			}
			
			/*
			 * Upon initial choice of materialize mode, seize the tuplestore.
			 */
			if (tuplestorestate == NULL)
			{
				scanstate->tuplestorestate = rsinfo->setResult;
				tuplestorestate = rsinfo->setResult;
				Assert(tuplestorestate);
				rsinfo->setResult = NULL;
			}

			/*
			 * Single-tuplestore case.	Fetch and return the first of the
			 * newly appended tuples.  The caller will read the rest, then
			 * call again for more.  (There could be more if there is a
			 * set-valued argument, or if the function doles out its results
			 * over a series of calls by setting ExprMultipleResult.)
			 */
			if (rsinfo->setResult == NULL)
			{
				if (tuplestore_gettupleslot(tuplestorestate, true, false, slot))
					return true;
			}

			/*
			 * Double-tuplestore case.	Functions can still use the older
			 * variant of the materialize mode protocol, in which they don't
			 * look for a retained tuplestore pointer in rsinfo->setResult,
			 * but simply create a new tuplestore on every call.
			 *
			 * If the function was given a tuplestore but ignored it and
			 * substituted its own, overwriting the given pointer, we'll
			 * consider it uncooperative, and proceed with two tuplestores.
			 *
			 * Each time we are called, we read one tuple from the function's
			 * (new) tuplestore, append it to the caller's (old) tuplestore,
			 * and return the tuple.  In the caller's tuplestore the read
			 * position remains at eof and we insert each new tuple just
			 * before that.  When the caller reads again from the tuplestore,
			 * it will hit eof immediately and we'll be called again, handling
			 * one tuple per call.
			 */
			else
			{
				/* Nudge caller's read position onto eof as it was before. */
				if (nudge)
					tuplestore_advance(tuplestorestate, true);

				/* Fetch and return the first of the newly appended tuples. */
				if (tuplestore_gettupleslot(rsinfo->setResult, true, false, slot))
				{
					tuplestore_puttupleslot(tuplestorestate, slot);
					return true;
				}
			}

			/*
			 * The function returned without adding so much as one tuple to
			 * the tuplestore.	There are no more results for the current
			 * values of the arguments.  Make sure ExprMultipleResult is
			 * turned off, so the arguments are unfrozen and can advance.
			 */
			rsinfo->isDone = ExprSingleResult;

			/*
			 * Loop to call ExecEvalFuncSRF() again. In the event there is a
			 * set-valued argument that is not yet exhausted, it will advance
			 * the argument to its next value and call the function again to
			 * append more result tuples.
			 */
		}
	}

	/*
	 * If the function doesn't return SETOF then the planner might have
	 * replaced the function call via constant-folding or inlining.  So if we
	 * see any other kind of expression node, execute it here via the general
	 * ExecEvalExpr() code.  We also come here for SRFs that have previously
	 * returned a result in value-per-call mode, and for functions that are
	 * not set-returning: all can be called by ordinary ExecEvalExpr().
	 */
	else
	{
		/* Call the function. */
		result = ExecEvalExpr(scanstate->funcexpr, econtext, &isNull, &isDone);

		/* Quit if empty set or end of set. */
		if (isDone == ExprEndResult)
		{
			ExecClearTuple(slot);
			return false;
		}

		/*
		 * If result is of composite or RECORD type, fail if the actual tuple
		 * format is incompatible with the output slot's expected tupdesc.
		 * Skip if expr is a function, because ExecEvalFunc or ExecEvalSRF
		 * checked this already.
		 */
		if (!isNull &&
			scanstate->returnsTuple &&
			!IsA(scanstate->funcexpr, FuncExprState))
			result = ExecVerifyReturnedRowType((Expr *) scanstate->funcexpr,
											   result,
											   slot->tts_tupleDescriptor,
											   &scanstate->returnedTypeId,
											   &scanstate->returnedTypMod);
	}

	/* Store result of value-per-call or non-SRF function into the slot. */
	ExecStoreSlotTupleDatum(slot, result, isNull, scanstate->returnsTuple);

	/* Create tuplestore in query-lifetime memory context. */
	if (!tuplestorestate)
	{
		MemoryContext	oldcontext;

		oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);

		tuplestorestate = tuplestore_begin_heap(scanstate->randomAccess, false, work_mem);
		tuplestore_advance(tuplestorestate, true);		/* forward onto eof */

		MemoryContextSwitchTo(oldcontext);

		/* Give the tuplestore to caller. */
		scanstate->tuplestorestate = tuplestorestate;
	}

	/*
	 * Append a copy of the returned tuple to the tuplestore. Given that the
	 * tuplestore is in EOF state, its read position will remain at EOF,
	 * beyond the added tuple.	When the caller tries to read from the
	 * tuplestore, it will see EOF and call us again to get the next tuple.
	 */
	tuplestore_puttupleslot(tuplestorestate, slot);
	return true;
}

/*
 *		ExecEvalFuncDematerialize
 *
 * Evaluate the arguments to a set-returning function, and then the
 * function itself.
 *
 * This routine can handle set-returning functions having at most one
 * set-valued argument.
 *
 * This routine provides a uniform interface to set-returning functions
 * regardless of whether they use value-per-call or materialize mode.
 * If the function returns its result set in a tuplestore, we fetch and
 * return one value per call from the tuplestore.
 *
 * But if the function uses value-per-call mode, the lower-level function
 * ExecEvalFuncSRF does everything necessary; so to shorten the path, we'll
 * make ExecEvalExpr go there directly on subsequent calls, by changing the
 * FuncExprState function pointer.
 */
static Datum
ExecEvalFuncDematerialize(FuncExprState *fcache,
						  ExprContext *econtext,
						  bool *isNull,
						  ExprDoneCond *isDone)
{
	ReturnSetInfo  *rsinfo = &fcache->rsinfo;
	Datum			result;
	MemoryContext	oldcontext;
	bool			detectempty = false;

	/* Caller has to participate in the internal value-per-call protocol. */
	if (!isDone)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("set-valued function called in context that cannot accept a set"),
				 func_expr_errcontext(fcache->xprstate.expr, false)));

	/* Once-per-query initialization. */
	if (fcache->func.fn_oid == InvalidOid)
	{
		Expr *expr = fcache->xprstate.expr;

		/* Look up the function entry point and check permissions. */
		if (IsA(expr, FuncExpr))
		{
			FuncExpr *func = (FuncExpr *) expr;

			init_fcache(func->funcid, func->inputcollid, fcache, econtext);
		}
		else
		{
			OpExpr *op = (OpExpr *) expr;

			Assert(IsA(expr, OpExpr));
			init_fcache(op->opfuncid, op->inputcollid, fcache, econtext);
		}

		/* Only set-returning functions are handled here. */
		Assert(fcache->func.fn_retset);

		/* Initially the function can choose either mode to return results. */
		rsinfo->allowedModes = SFRM_ValuePerCall | SFRM_Materialize;

		/* Build expected result tuple descriptor. */
		oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
		get_expr_result_tupdesc((Expr *) fcache->func.fn_expr,
								NULL,
								&fcache->rsinfo.expectedDesc,
								&fcache->funcReturnsTuple);
		MemoryContextSwitchTo(oldcontext);
	}

	for (;;)
	{
		Tuplestorestate	*tuplestore = rsinfo->setResult;

		/* Return next result value from tuplestore. */
		if (tuplestore)
		{
			if (tuplestore_gettupleslot(tuplestore, true, false,
										fcache->dematerializeSlot))
			{
				/* Must we return the whole tuple as a Datum? */
				if (fcache->funcReturnsTuple)
				{
					*isNull = false;
					result = ExecFetchSlotTupleDatum(fcache->dematerializeSlot);
				}

				/* Extract the first column and return it as a scalar. */
				else
					result = slot_getattr(fcache->dematerializeSlot, 1, isNull);

				/* Let the query be canceled in case the result set is large. */
				CHECK_FOR_INTERRUPTS();

				*isDone = ExprMultipleResult;
				return result;
			}

			/*
			 * Exhausted the tuplestore.  Reset it to empty, but keep it for
			 * possible reuse.
			 */
			tuplestore_clear(tuplestore);

			/*
			 * If the function returned without adding at least one tuple to
			 * the tuplestore, then do not continue to call it with the same
			 * arguments.  Turn off ExprMultipleResult and resume normal mode.
			 */
			if (detectempty)
				rsinfo->isDone = ExprSingleResult;
		}

		/*
		 * Call the function, getting back either the next Datum (or NULL); or
		 * the (maybe empty) result set in a tuplestore; or end-of-set.
		 */
		result = ExecEvalFuncSRF(fcache, econtext, isNull, isDone);

		/* At end of set, return. */
		if (*isDone == ExprEndResult)
			return result;

		/* Free old tuplestore if function ignored it and created a new one. */
		if (tuplestore != NULL &&
			tuplestore != rsinfo->setResult)
			tuplestore_end(tuplestore);

		/*
		 * The function has decided its mode (value-per-call or materialize)
		 * and now the choice is final.  Upon first returning a nonempty
		 * result in value-per-call mode, we change the ExecEvalExpr function
		 * pointer so subsequent calls go directly to ExecEvalFuncSRF.
		 *
		 * The function's choice of mode must be considered undecided until we
		 * have called and gotten something back.  A function doesn't have to
		 * declare its choice until it has something to return.  Also, with an
		 * empty result (*isDone == ExprEndResult) it is possible that the
		 * function has not been called, either because it has an empty
		 * set-valued argument, or it is strict and has a null argument.
		 */
		if (rsinfo->returnMode == SFRM_ValuePerCall)
		{
			/*
			 * In case function created a tuplestore before value-per-call
			 * mode was chosen, free it.  It should be empty.  Not an error.
			 */
			if (rsinfo->setResult)
			{
				tuplestore_end(rsinfo->setResult);
				rsinfo->setResult = NULL;
			}

			/* Next time, skip this routine and go straight to lower level. */
			fcache->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFuncSRF;

			/* Return value-per-call Datum, or *isNull == true for null. */
			Assert(*isDone == ExprMultipleResult);
			return result;
		}

		/* ExecEvalFuncSRF made sure we have tuplestore & expectedDesc. */
		Assert(rsinfo->returnMode == SFRM_Materialize &&
			   rsinfo->setResult != NULL &&
			   rsinfo->expectedDesc != NULL);

		/* Create a slot so we can read data out of the tuplestore. */
		if (!fcache->dematerializeSlot)
		{
			oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
			fcache->dematerializeSlot = MakeSingleTupleTableSlot(rsinfo->expectedDesc);
			MemoryContextSwitchTo(oldcontext);
		}

		/* We'll soon know whether the function produced any tuples. */
		detectempty = true;
	}
}

/*
 *		ExecEvalFuncSRF
 *
 * Evaluate the arguments to a set-returning function, and then the function
 * itself.	init_fcache must have already run on the FuncExprState.
 *
 * This routine can handle set-returning functions having at most one
 * set-valued argument.
 *
 * For a set-returning function which uses value-per-call mode, this routine
 * returns the results using the usual internal value-per-call protocol.
 *
 * For a set-returning function which uses materialize mode, we return with
 * fcache->rsinfo.setResult pointing to the tuplestore containing the result.
 * The caller takes charge of the tuplestore and must eventually free it.
 *
 * If a function uses materialize mode and is called with a non-null
 * tuplestore pointer in rsinfo->setResult, then it may either append
 * its results to the given tuplestore, or ignore it and overwrite the
 * setResult field with a new tuplestore pointer or NULL.  The function
 * must not call tuplestore_end() on a tuplestore pointer that it has
 * either received or returned via rsinfo->setResult; that will be the
 * caller's responsibility.
 */
static Datum
ExecEvalFuncSRF(FuncExprState *fcache,
				ExprContext *econtext,
				bool *isNull,
				ExprDoneCond *isDone)
{
	FunctionCallInfo fcinfo = &fcache->fcinfo_data;
	MemoryContext callercxt;

	/* init_fcache has been called to initialize the FuncExprState. */
	Assert(fcache->func.fn_oid != InvalidOid);

	/* Only set-returning functions are handled here. */
	Assert(fcache->func.fn_retset);

	/* Caller has to cooperate in the internal value-per-call protocol. */
	if (!isDone)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("set-valued function called in context that cannot accept a set"),
				 func_expr_errcontext(fcache->xprstate.expr, false)));

	/* Guard against stack overflow due to overly complex expressions. */
	check_stack_depth();

	/*
	 * If caller wants next result from a function that requested to be called
	 * again, don't re-evaluate the arguments.  On this call, we'll pass the
	 * same arguments as last time: the old values remain in fcinfo from the
	 * previous call.
	 *
	 * (Note:  If the function has not yet been called, or if it didn't
	 * request another call, then rsinfo.isDone == ExprSingleResult.  If the
	 * previous call returned end-of-set, then rsinfo.isDone ==
	 * ExprEndResult.)
	 */
	if (fcache->rsinfo.isDone == ExprMultipleResult)
	{
		Assert(fcache->argIsDone != ExprEndResult);
		fcinfo->isnull = false;
	}

	/*
	 * If the function returned ExprSingleResult on the previous call, we'll
	 * return end-of-set this time, unless there is a set-valued argument
	 * which could produce more values.
	 *
	 * (This can't occur on the initial call, or after returning end-of-set
	 * for given argument values, because then argIsDone == ExprEndResult.)
	 */
	else if (fcache->argIsDone == ExprSingleResult &&
			 fcache->rsinfo.isDone == ExprSingleResult)
		fcache->argIsDone = ExprEndResult;

	/*
	 * Evaluate the arguments, storing values and null flags into fcinfo.
	 * fcinfo->isNull will be set if function is strict and has a NULL arg.
	 *
	 * Argument values are allocated in a private memory context so they can
	 * remain unchanged across a series of value-per-call invocations.
	 */
	else
	{
		/* Create memory context for argument evaluation, on first call. */
		if (!fcache->argEvalContext)
		{
			fcache->argEvalContext =
				AllocSetContextCreate(fcache->func.fn_mcxt,
									  "argEvalContext",
									  ALLOCSET_SMALL_MINSIZE,
									  ALLOCSET_SMALL_INITSIZE,
									  ALLOCSET_SMALL_MAXSIZE);
		}

		/* Register callback to reset for rescan and clean up at end of query */
		if (!fcache->shutdown_reg)
		{
			fcache->shutdown_reg = true;
			RegisterExprContextCallback(econtext, ShutdownFuncExpr,
										PointerGetDatum(fcache));
		}

		/* Free pass-by-reference outputs (and garbage) of last evaluation. */
		MemoryContextReset(fcache->argEvalContext);

		/* Evaluate the arguments. */
		callercxt = MemoryContextSwitchTo(fcache->argEvalContext);
		fcache->argIsDone = ExecEvalFuncArgs(fcinfo, fcache->args, econtext);
		MemoryContextSwitchTo(callercxt);
	}

	/*
	 * This loop handles the situation where we have both a set argument and a
	 * set-valued function.  Once we have exhausted the function's value(s)
	 * for a particular argument value, we have to get the next argument value
	 * and start the function over again. We might have to do it more than
	 * once, if the function produces an empty result set for a particular
	 * input value.
	 */
	while (fcache->argIsDone != ExprEndResult)
	{
		/*
		 * Call a set-returning function.  But if it is strict and has a NULL
		 * argument, skip the call and act like it returned an empty set.
		 */
		if (!fcinfo->isnull)
		{
			Datum			result;
			ReturnSetInfo	*rsinfo = &fcache->rsinfo;
			Tuplestorestate	*callertupstore = rsinfo->setResult;
			PgStat_FunctionCallUsage fcusage;

			/* Start timing. */
			pgstat_init_function_usage(fcinfo, &fcusage);

			/*
			 * Make the call.
			 */
			result = FunctionCallInvoke(fcinfo);

			/* Stop timing. */
			pgstat_end_function_usage(&fcusage,
									  rsinfo->isDone != ExprMultipleResult);

			/* Verify that some of the read-only fields remain unchanged. */
			Assert(fcinfo->resultinfo == (fmNodePtr) rsinfo &&
				   IsA(rsinfo, ReturnSetInfo));
			Assert(econtext == rsinfo->econtext &&
				 fcinfo->flinfo->fn_mcxt == econtext->ecxt_per_query_memory);

			/*
			 * If the function filled in setDesc, verify with expectedDesc.
			 *
			 * A function returning a composite or RECORD type may pass back
			 * its result tuple descriptor via the rsinfo->setDesc field
			 * (deprecated) or srf_verify_expected_tupdesc() (preferred). This
			 * is mandatory for use of materialize mode when the caller has
			 * not provided an expected descriptor via rsinfo->expectedDesc (a
			 * possibility if the return type is RECORD with no OUT or INOUT
			 * parameters).  Otherwise it's just a sanity check - recommended
			 * for materialize mode - to raise an error if the actual result
			 * tuple format isn't binary compatible with the expected format.
			 *
			 * Value-per-call mode can use this too, but it's unnecessary
			 * because each returned tuple will have its descriptor checked.
			 *
			 * We free the setDesc right away.	Functions shouldn't go to the
			 * trouble of allocating it in some longer-lived memory context.
			 * It might be nice if functions could use the setDesc field to
			 * keep their descriptor across calls; but no: some old functions
			 * were accustomed to overwriting setDesc with new descriptors on
			 * every call, which have to be freed here or they'll pile up in
			 * the per-query memory context.
			 */
			if (rsinfo->setDesc)
			{
				ExecVerifyExpectedTupleDesc(fcinfo, rsinfo->setDesc);
				if (rsinfo->setDesc->tdrefcount == -1)
					FreeTupleDesc(rsinfo->setDesc);
				else
					ReleaseTupleDesc(rsinfo->setDesc);
				rsinfo->setDesc = NULL;
			}

			/*
			 * Did the function produce a result?
			 *
			 * No result value is expected from a call when the function
			 * signals ExprEndResult.  Also, the function doesn't have to
			 * choose between value-per-call mode or materialize mode until
			 * the first time it uses ExprSingleResult or ExprMultipleResult.
			 */
			if (rsinfo->isDone == ExprEndResult)
			{
				/*
				 * If the function appears to have made a new tuplestore,
				 * overwriting an older non-NULL tuplestore pointer, discard
				 * the new and retain the old.	(Otherwise tuplestores could
				 * be orphaned and leak while iterating over a set-valued
				 * argument.)  The discarded tuplestore can be assumed empty,
				 * because no results can accompany ExprEndResult.	It's not
				 * an error: a function may create its tuplestore before it
				 * decides that it has no results to return; we allow such a
				 * tuplestore to remain for later use unless it would orphan
				 * an older tuplestore.  It's ok (but redundant) for an SRF to
				 * clear the setResult field when signaling ExprEndResult.
				 * Note that a function mustn't call tuplestore_end() on a
				 * pointer which it has received or returned in setResult.
				 */
				if (callertupstore &&
					rsinfo->setResult != callertupstore)
				{
					if (rsinfo->setResult)
						tuplestore_end(rsinfo->setResult);
					rsinfo->setResult = callertupstore;
				}
			}
			
			/*
			 * Does the function want to use value-per-call mode?
			 *
			 * NB. The setResult field isn't used in the value-per-call
			 * protocol, but it could contain a tuplestore pointer that the
			 * caller gave for use in case materialize mode might be chosen.
			 */
			else if (rsinfo->returnMode == SFRM_ValuePerCall)
			{
				/* Fail if function has previously used materialize mode. */
				if (!(rsinfo->allowedModes & SFRM_ValuePerCall))
					ereport(ERROR,
							(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
							 errmsg("table-function protocol was not followed"),
							 errhint("cannot switch to value-per-call mode after "
									 "returning results in materialize mode"),
							 fmgr_call_errcontext(fcinfo, true)));

				/* Disallow materialize mode for subsequent calls. */
				rsinfo->allowedModes &= ~SFRM_Materialize &
										~SFRM_Materialize_Preferred &
										~SFRM_Materialize_Random;

				/* Fail if composite or RECORD type result has wrong format. */
				if (fcache->funcReturnsTuple &&
					!fcinfo->isnull)
					result = ExecVerifyReturnedRowType((Expr *)fcache, result,
													   rsinfo->expectedDesc,
													   &fcache->returnedTypeId,
													   &fcache->returnedTypMod);

				/* Let query be canceled in case of endless result set. */
				CHECK_FOR_INTERRUPTS();

				/* Return result to caller. */
				*isDone = ExprMultipleResult;
				*isNull = fcinfo->isnull;
				return result;
			}

			/*
			 * Does the function want to use materialize (set-per-call) mode?
			 */
			else if (rsinfo->returnMode == SFRM_Materialize)
			{
				/* Materialize mode doesn't use the fcinfo->isnull field. */

				/* Fail if the function previously used value-per-call mode. */
				if (!(rsinfo->allowedModes & SFRM_Materialize))
					ereport(ERROR,
							(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
						     errmsg("table-function protocol was not followed"),
							 errhint("cannot switch to materialize mode after "
									 "returning results in value-per-call mode"),
							 fmgr_call_errcontext(fcinfo, true)));

				/* Disallow value-per-call mode for subsequent calls. */
				rsinfo->allowedModes &= ~SFRM_ValuePerCall;

				/*
				 * If setResult comes back NULL, it means an empty result set,
				 * the same as ExprEndResult.
				 *
				 * The function must never free a tuplestore provided by the
				 * caller and passed to the function in the rsinfo->setResult
				 * field.  But it's alright for the function to ignore any
				 * incoming pointer in setResult and overwrite it with NULL
				 * for emptiness.  If this appears to have happened, restore
				 * the earlier setResult.
				 */
				if (rsinfo->setResult == NULL)
					rsinfo->setResult = callertupstore;

				/*
				 * If the function returned a tuplestore containing its result
				 * set - empty or not - hand it over to the caller.  Likewise
				 * if the function continued using a tuplestore provided by
				 * the caller or remaining from an earlier iteration.  The
				 * function is allowed to ignore any incoming pointer in
				 * setResult and overwrite it with a new tuplestore pointer of
				 * its own; the caller must cope with this eventuality.
				 *
				 * Without reading from the tuplestore, we don't know whether
				 * anything has been put into it.
				 *
				 * NB: If a tuplestore pointer remains in setResult at the
				 * time our ShutdownFuncExpr callback is executed, it will
				 * free that tuplestore.  Callers who keep their own pointers
				 * must take care that each tuplestore is freed exactly once.
				 */
				else
				{
					/*
					 * If we were not able to determine the result rowtype
					 * from context, and the function didn't return a tupdesc,
					 * we can't read from the tuplestore and have to fail.
					 */
					if (!rsinfo->expectedDesc)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("function returning record called in "
								   "context that cannot accept type record"),
								 fmgr_call_errcontext(fcinfo, false)));

					/* Let query be canceled in case of endless result set. */
					CHECK_FOR_INTERRUPTS();

					/* Return to caller with the tuplestore ptr in setResult. */
					*isDone = rsinfo->isDone;
					*isNull = false;
					return (Datum) 0;
				}
			}
			else
				ereport(ERROR,
						(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
						 errmsg("unrecognized table-function returnMode: %d",
								(int) rsinfo->returnMode),
						 fmgr_call_errcontext(fcinfo, true)));
		}

		/*
		 * No result values were obtained given the current argument values.
		 * We're done, unless one of the arguments is a set-valued expression
		 * which might yield another value.
		 */
		if (fcache->argIsDone != ExprMultipleResult)
			break;

		/* Discard pass-by-reference outputs and garbage from last arg eval. */
		MemoryContextReset(fcache->argEvalContext);

		/* Evaluate args again to obtain next element of the set-valued arg. */
		callercxt = MemoryContextSwitchTo(fcache->argEvalContext);
		fcache->argIsDone = ExecEvalFuncArgs(fcinfo, fcache->args, econtext);
		Assert(fcache->argIsDone != ExprSingleResult);
		MemoryContextSwitchTo(callercxt);
	}

	/* Discard any pass-by-reference outputs and garbage from last arg eval. */
	MemoryContextReset(fcache->argEvalContext);

	/*
	 * No more results.  Return end-of-set.
	 *
	 * The caller now can change some inputs to the expression and call again,
	 * beginning a new cycle.
	 */
	Assert(fcache->rsinfo.isDone != ExprMultipleResult);
	fcache->argIsDone = ExprEndResult;
	*isDone = ExprEndResult;
	*isNull = true;
	return (Datum) 0;
}


/*
 * init_fcache - initialize a FuncExprState node during first use
 *
 * Before calling this routine, the caller must initialize the fields
 * fcache->xprstate.expr and fcache->args.  The only other field customarily
 * initialized by the caller is fcache->func.fn_oid = InvalidOid.
 */
static void
init_fcache(Oid foid, Oid input_collation, FuncExprState *fcache, ExprContext *econtext)
{
	ReturnSetInfo *rsinfo;
	AclResult	aclresult;

	/* Check permission to call function */
	aclresult = pg_proc_aclcheck(foid, GetUserId(), ACL_EXECUTE);
	if (aclresult != ACLCHECK_OK)
		aclcheck_error(aclresult, ACL_KIND_PROC, get_func_name(foid));

	/*
	 * Safety check on nargs.  Under normal circumstances this should never
	 * fail, as parser should check sooner.  But possibly it might fail if
	 * server has been compiled with FUNC_MAX_ARGS smaller than some functions
	 * declared in pg_proc?
	 */
	if (list_length(fcache->args) > FUNC_MAX_ARGS)
		ereport(ERROR,
				(errcode(ERRCODE_TOO_MANY_ARGUMENTS),
			 errmsg_plural("cannot pass more than %d argument to a function",
						   "cannot pass more than %d arguments to a function",
						   FUNC_MAX_ARGS,
						   FUNC_MAX_ARGS)));

	/* Set up the primary fmgr lookup information */
	fmgr_info_cxt(foid, &fcache->func, econtext->ecxt_per_query_memory);
	fmgr_info_set_expr((Node *) fcache->xprstate.expr, &(fcache->func));

	/* Initialize state for evaluation of set-valued arguments. */
	fcache->argIsDone = ExprEndResult;

	/* Initialize resultinfo. */
	rsinfo = &fcache->rsinfo;
	rsinfo->type = T_ReturnSetInfo;
	rsinfo->econtext = econtext;
	rsinfo->expectedDesc = NULL;
	rsinfo->allowedModes = 0;
	rsinfo->returnMode = SFRM_ValuePerCall;
	rsinfo->isDone = ExprSingleResult;
	rsinfo->setResult = NULL;
	rsinfo->setDesc = NULL;

	/* Initialize the rest. */
	fcache->funcReturnsTuple = false;
	fcache->returnedTypeId = InvalidOid;
	fcache->returnedTypMod = 0;
	fcache->argEvalContext = NULL;
	fcache->dematerializeSlot = NULL;
	fcache->shutdown_reg = false;

	/*
	 * Set up the parameter block that will be passed to the function.
	 * Always pass ReturnSetInfo; it's cheap.  Some functions might want
	 * access to the econtext so they can request a cleanup callback.
	 */
	InitFunctionCallInfoData(fcache->fcinfo_data,
							 &fcache->func,
							 list_length(fcache->args),
							 input_collation,
							 NULL,
							 (fmNodePtr) rsinfo);
}


/*
 * Evaluate arguments for a function.
 *
 * Sets fcinfo->isNull = true if function is strict and some argument is NULL,
 * otherwise false.
 */
static ExprDoneCond
ExecEvalFuncArgs(FunctionCallInfo fcinfo, List *argList, ExprContext *econtext)
{
	ExprDoneCond argIsDone;
	ListCell   *arg;
	int			i;

	argIsDone = ExprSingleResult;		/* default assumption */
	fcinfo->isnull = false;

	i = 0;
	foreach(arg, argList)
	{
		ExprState  *argstate = (ExprState *) lfirst(arg);
		ExprDoneCond thisArgIsDone;

		fcinfo->arg[i] = ExecEvalExpr(argstate,
									  econtext,
									  &fcinfo->argnull[i],
									  &thisArgIsDone);

		if (fcinfo->argnull[i] && fcinfo->flinfo->fn_strict)
			fcinfo->isnull = true;

		if (thisArgIsDone != ExprSingleResult)
		{
			/*
			 * We allow only one argument to have a set value; we'd need much
			 * more complexity to keep track of multiple set arguments (cf.
			 * ExecTargetList) and it doesn't seem worth it.
			 */
			if (argIsDone != ExprSingleResult)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("functions and operators can take at most one set argument"),
						 fmgr_call_errcontext(fcinfo, false)));
			argIsDone = thisArgIsDone;
		}
		i++;
	}
	return argIsDone;
}


/* ----------------------------------------------------------------
 *		ExecEvalFunc
 *
 * Evaluate the arguments to a non-set-returning function, and then the
 * function itself.
 *
 * This routine can handle non-set-returning functions having at most one
 * set-valued argument.  On the first call, if there is no set-valued
 * argument, we'll change the FuncExprState's function pointer to steer
 * ExecEvalExpr to the faster ExecEvalFuncSimple* for subsequent calls.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalFunc(FuncExprState *fcache,
			 ExprContext *econtext,
			 bool *isNull,
			 ExprDoneCond *isDone)
{
	Datum		result;
	FunctionCallInfo fcinfo = &fcache->fcinfo_data;

	/* Guard against stack overflow due to overly complex expressions. */
	check_stack_depth();

	/*
	 * On first call, look up the function entry point and check permissions.
	 * Complete the initialization of our FuncExprState node.  This could have
	 * been done in ExecInitExpr, but by deferring it until now, we save a
	 * little time in case the expression is never evaluated.
	 */
	if (fcache->func.fn_oid == InvalidOid)
	{
		Expr *expr = fcache->xprstate.expr;
		Oid resulttype;

		if (IsA(expr, FuncExpr))
		{
			FuncExpr *func = (FuncExpr *) fcache->xprstate.expr;

			init_fcache(func->funcid, func->inputcollid, fcache, econtext);
			resulttype = func->funcresulttype;
		}
		else
		{
			OpExpr *op = (OpExpr *) expr;

			Assert(IsA(expr, OpExpr));
 			init_fcache(op->opfuncid, op->inputcollid, fcache, econtext);
			resulttype = op->opresulttype;
		}

		/* Only non-set-returning functions are handled here. */
		Assert(!fcache->func.fn_retset);

		/*
		 * If function returns RECORD, see if it has OUT and/or INOUT
		 * parameters defining its result tuple format; if so, build an
		 * expected tuple descriptor so the actual result tuple format can be
		 * validated.  (It would be nice to do this for "composite" types
		 * also, but to detect those would cost another typcache lookup; maybe
		 * revisit this later.)
		 */
		if (resulttype == RECORDOID)
		{
			MemoryContext oldcontext;

			oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
			get_expr_result_tupdesc(expr, NULL,	&fcache->rsinfo.expectedDesc,
									&fcache->funcReturnsTuple);
			MemoryContextSwitchTo(oldcontext);
		}
	}

	/*
	 * Evaluate function arguments.  Store values and null flags into fcinfo.
	 * Set fcinfo->isNull if function is strict and has a NULL argument.
	 */
	fcache->argIsDone = ExecEvalFuncArgs(fcinfo, fcache->args, econtext);

	/*
	 * If function has a set-valued argument, this expr becomes set-valued.
	 */
	if (fcache->argIsDone != ExprSingleResult)
	{
		/* Yield empty set result if an empty set-valued argument was found. */
		if (fcache->argIsDone == ExprEndResult)
			fcinfo->isnull = true;

		/* Fail if caller doesn't handle internal value-at-a-time protocol. */
		if (!isDone)
			ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							errmsg("set-valued function called in context that cannot accept a set"),
							func_expr_errcontext(fcache->xprstate.expr, false)));
	}

	/*
	 * An expr should return a set always or never.  Therefore if none of the
	 * arguments returned a set on the first call, we can change the ExprState
	 * function pointer to use one of the ExecEvalFuncSimple* routines from
	 * now on.  But we stick with this routine in some less frequent cases, to
	 * minimize the path length of the fast-path Simple* routines.
	 */
	else if (!fcache->funcReturnsTuple &&
			 pgstat_track_functions <= fcinfo->flinfo->fn_stats)
	{
		if (fcache->func.fn_strict && fcinfo->nargs == 2)
			fcache->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFuncSimple2;
		else
			fcache->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFuncSimpleN;
	}

	/*
	 * Return NULL if the function is strict and has a NULL argument.
	 */
	if (fcinfo->isnull)
		result = (Datum) 0;

	/*
	 * Call the function.
	 */
	else
	{
		PgStat_FunctionCallUsage fcusage;

		/* Start timing. */
		pgstat_init_function_usage(fcinfo, &fcusage);

		/* Call the function. */
		result = FunctionCallInvoke(fcinfo);

		/* Stop timing. */
		pgstat_end_function_usage(&fcusage, true);

		/*
		 * Fail if non-set-returning function tries to return a set.
		 * Non-set-returning functions shouldn't touch setResult.
		 */
		if (fcache->rsinfo.isDone != ExprSingleResult ||
			fcache->rsinfo.returnMode != SFRM_ValuePerCall ||
			fcache->rsinfo.setResult != NULL)
			ereport(ERROR, (errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
							errmsg("A function cannot return a set unless created with the SETOF keyword"),
							fmgr_call_errcontext(fcinfo, true)));

		/*
		 * Fail if result is of composite or RECORD type and has wrong format.
		 * NB: For composites (cataloged row types), we left funcReturnsTuple
		 * unset, rather than lengthen the scalar path by one more typcache
		 * lookup which would be needed to detect that the type is composite.
		 */
		if (fcache->funcReturnsTuple && !fcinfo->isnull)
			result = ExecVerifyReturnedRowType((Expr *) fcache, result,
											   fcache->rsinfo.expectedDesc,
											   &fcache->returnedTypeId,
											   &fcache->returnedTypMod);
	}
	if (isDone)
		*isDone = fcache->argIsDone;
	*isNull = fcinfo->isnull;
	return result;
}

/*
 *		ExecEvalFuncSimple2
 *
 * Call a strict, non-set-returning function of exactly 2 non-set-valued args.
 */
static Datum
ExecEvalFuncSimple2(FuncExprState *fcache,
			 ExprContext *econtext,
			 bool *isNull,
			 ExprDoneCond *isDone)
{
	FunctionCallInfo fcinfo = &fcache->fcinfo_data;
	ListCell	*arg;
	Datum		result;

	/* init_fcache has been called to initialize the FuncExprState. */
	Assert(fcache->func.fn_oid != InvalidOid);

	/* We handle only non-set-returning, strict functions of two args. */
	Assert(!fcache->func.fn_retset &&
		   fcache->func.fn_strict &&
		   list_length(fcache->args) == 2);

	/* When timing function execution, we don't use this fast path. */
	Assert(pgstat_track_functions <= fcache->func.fn_stats);

	/* Guard against stack overflow due to overly complex expressions. */
	check_stack_depth();

	if (isDone)
		*isDone = ExprSingleResult;

	/* Evaluate first argument. */
	arg = fcache->args->head;
	fcinfo->arg[0] = ExecEvalExpr((ExprState *) lfirst(arg),
									econtext,
									&fcinfo->argnull[0],
									NULL);

	/* Evaluate second argument. */
	fcinfo->arg[1] = ExecEvalExpr((ExprState *) lfirst(lnext(arg)),
									econtext,
									&fcinfo->argnull[1],
									NULL);

	/* If function has a null argument, skip call and return null. */
	if (fcinfo->argnull[0] || fcinfo->argnull[1])
	{
		*isNull = true;
		return (Datum) 0;
	}

	/* Call the function. */
	fcinfo->isnull = false;
	result = FunctionCallInvoke(fcinfo);
	*isNull = fcinfo->isnull;
	return result;
}

/*
 *		ExecEvalFuncSimpleN
 *
 * This routine handles functions that do not themselves return sets, and
 * do not have set-valued arguments; thus yielding a single Datum or NULL.
 */
static Datum
ExecEvalFuncSimpleN(FuncExprState *fcache,
			 ExprContext *econtext,
			 bool *isNull,
			 ExprDoneCond *isDone)
{
	FunctionCallInfo fcinfo = &fcache->fcinfo_data;
	Datum		result;
	ListCell   *arg;
	int			i;

	/* init_fcache has been called to initialize the FuncExprState. */
	Assert(fcache->func.fn_oid != InvalidOid);

	/* Only non-set-returning functions are handled here. */
	Assert(!fcache->func.fn_retset);

	/* When timing function execution, we don't use this fast path. */
	Assert(pgstat_track_functions <= fcache->func.fn_stats);

	/* Guard against stack overflow due to overly complex expressions */
	check_stack_depth();

	if (isDone)
		*isDone = ExprSingleResult;

	/* Evaluate args. (An inlined, simplified version of ExecEvalFuncArgs.) */
	i = 0;
	fcinfo->isnull = false;
	foreach(arg, fcache->args)
	{
		ExprState  *argstate = (ExprState *) lfirst(arg);

		fcinfo->arg[i] = ExecEvalExpr(argstate,
									  econtext,
									  &fcinfo->argnull[i],
									  NULL);
		if (fcinfo->argnull[i] && fcache->func.fn_strict)
			fcinfo->isnull = true;
		i++;
	}

	/* If strict function has a null argument, skip call and return null. */
	if (fcinfo->isnull)
		result = (Datum) 0;

	/* Call the function. */
	else
		result = FunctionCallInvoke(fcinfo);

	*isNull = fcinfo->isnull;
	return result;
}


/* ----------------------------------------------------------------
 *		ExecEvalDistinct
 *
 * IS DISTINCT FROM must evaluate arguments to determine whether
 * they are NULL; if either is NULL then the result is already
 * known. If neither is NULL, then proceed to evaluate the
 * function. Note that this is *always* derived from the equals
 * operator, but since we need special processing of the arguments
 * we can not simply reuse ExecEvalOper() or ExecEvalFunc().
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalDistinct(FuncExprState *fcache,
				 ExprContext *econtext,
				 bool *isNull,
				 ExprDoneCond *isDone)
{
	Datum		result;
	FunctionCallInfo fcinfo;
	ExprDoneCond argDone;

	/* Set default values for result flags: non-null, not a set result */
	*isNull = false;
	if (isDone)
		*isDone = ExprSingleResult;

	/*
	 * Initialize function cache if first time through
	 */
	if (fcache->func.fn_oid == InvalidOid)
	{
		DistinctExpr *op = (DistinctExpr *) fcache->xprstate.expr;

		init_fcache(op->opfuncid, op->inputcollid, fcache, econtext);
		Assert(!fcache->func.fn_retset);
	}

	/*
	 * Evaluate arguments
	 */
	fcinfo = &fcache->fcinfo_data;
	argDone = ExecEvalFuncArgs(fcinfo, fcache->args, econtext);
	if (argDone != ExprSingleResult)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("IS DISTINCT FROM does not support set arguments")));
	Assert(fcinfo->nargs == 2);

	if (fcinfo->argnull[0] && fcinfo->argnull[1])
	{
		/* Both NULL? Then is not distinct... */
		result = BoolGetDatum(FALSE);
	}
	else if (fcinfo->argnull[0] || fcinfo->argnull[1])
	{
		/* Only one is NULL? Then is distinct... */
		result = BoolGetDatum(TRUE);
	}
	else
	{
		fcinfo->isnull = false;
		result = FunctionCallInvoke(fcinfo);
		*isNull = fcinfo->isnull;
		/* Must invert result of "=" */
		result = BoolGetDatum(!DatumGetBool(result));
	}

	return result;
}

/*
 * ExecEvalScalarArrayOp
 *
 * Evaluate "scalar op ANY/ALL (array)".  The operator always yields boolean,
 * and we combine the results across all array elements using OR and AND
 * (for ANY and ALL respectively).	Of course we short-circuit as soon as
 * the result is known.
 */
static Datum
ExecEvalScalarArrayOp(ScalarArrayOpExprState *sstate,
					  ExprContext *econtext,
					  bool *isNull, ExprDoneCond *isDone)
{
	ScalarArrayOpExpr *opexpr = (ScalarArrayOpExpr *) sstate->fxprstate.xprstate.expr;
	bool		useOr = opexpr->useOr;
	ArrayType  *arr;
	int			nitems;
	Datum		result;
	bool		resultnull;
	FunctionCallInfo fcinfo;
	ExprDoneCond argDone;
	int			i;
	int16		typlen;
	bool		typbyval;
	char		typalign;
	char	   *s;
	bits8	   *bitmap;
	int			bitmask;

	/* Set default values for result flags: non-null, not a set result */
	*isNull = false;
	if (isDone)
		*isDone = ExprSingleResult;

	/*
	 * Initialize function cache if first time through
	 */
	if (sstate->fxprstate.func.fn_oid == InvalidOid)
	{
		init_fcache(opexpr->opfuncid, opexpr->inputcollid, &sstate->fxprstate, econtext);
		Assert(!sstate->fxprstate.func.fn_retset);
	}

	/*
	 * Evaluate arguments
	 */
	fcinfo = &sstate->fxprstate.fcinfo_data;
	argDone = ExecEvalFuncArgs(fcinfo, sstate->fxprstate.args, econtext);
	if (argDone != ExprSingleResult)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
			   errmsg("op ANY/ALL (array) does not support set arguments")));
	Assert(fcinfo->nargs == 2);

	/*
	 * If the array is NULL then we return NULL --- it's not very meaningful
	 * to do anything else, even if the operator isn't strict.
	 */
	if (fcinfo->argnull[1])
	{
		*isNull = true;
		return (Datum) 0;
	}
	/* Else okay to fetch and detoast the array */
	arr = DatumGetArrayTypeP(fcinfo->arg[1]);

	/*
	 * If the array is empty, we return either FALSE or TRUE per the useOr
	 * flag.  This is correct even if the scalar is NULL; since we would
	 * evaluate the operator zero times, it matters not whether it would want
	 * to return NULL.
	 */
	nitems = ArrayGetNItems(ARR_NDIM(arr), ARR_DIMS(arr));
	if (nitems <= 0)
		return BoolGetDatum(!useOr);

	/*
	 * If the scalar is NULL, and the function is strict, return NULL; no
	 * point in iterating the loop.
	 */
	if (fcinfo->argnull[0] && sstate->fxprstate.func.fn_strict)
	{
		*isNull = true;
		return (Datum) 0;
	}

	/*
	 * We arrange to look up info about the element type only once per series
	 * of calls, assuming the element type doesn't change underneath us.
	 */
	if (sstate->element_type != ARR_ELEMTYPE(arr))
	{
		get_typlenbyvalalign(ARR_ELEMTYPE(arr),
							 &sstate->typlen,
							 &sstate->typbyval,
							 &sstate->typalign);
		sstate->element_type = ARR_ELEMTYPE(arr);
	}
	typlen = sstate->typlen;
	typbyval = sstate->typbyval;
	typalign = sstate->typalign;

	result = BoolGetDatum(!useOr);
	resultnull = false;

	/* Loop over the array elements */
	s = (char *) ARR_DATA_PTR(arr);
	bitmap = ARR_NULLBITMAP(arr);
	bitmask = 1;

	for (i = 0; i < nitems; i++)
	{
		Datum		elt;
		Datum		thisresult;

		/* Get array element, checking for NULL */
		if (bitmap && (*bitmap & bitmask) == 0)
		{
			fcinfo->arg[1] = (Datum) 0;
			fcinfo->argnull[1] = true;
		}
		else
		{
			elt = fetch_att(s, typbyval, typlen);
			s = att_addlength_pointer(s, typlen, s);
			s = (char *) att_align_nominal(s, typalign);
			fcinfo->arg[1] = elt;
			fcinfo->argnull[1] = false;
		}

		/* Call comparison function */
		if (fcinfo->argnull[1] && sstate->fxprstate.func.fn_strict)
		{
			fcinfo->isnull = true;
			thisresult = (Datum) 0;
		}
		else
		{
			fcinfo->isnull = false;
			thisresult = FunctionCallInvoke(fcinfo);
		}

		/* Combine results per OR or AND semantics */
		if (fcinfo->isnull)
			resultnull = true;
		else if (useOr)
		{
			if (DatumGetBool(thisresult))
			{
				result = BoolGetDatum(true);
				resultnull = false;
				break;			/* needn't look at any more elements */
			}
		}
		else
		{
			if (!DatumGetBool(thisresult))
			{
				result = BoolGetDatum(false);
				resultnull = false;
				break;			/* needn't look at any more elements */
			}
		}

		/* advance bitmap pointer if any */
		if (bitmap)
		{
			bitmask <<= 1;
			if (bitmask == 0x100)
			{
				bitmap++;
				bitmask = 1;
			}
		}
	}

	*isNull = resultnull;
	return result;
}

/* ----------------------------------------------------------------
 *		ExecEvalNot
 *		ExecEvalOr
 *		ExecEvalAnd
 *
 *		Evaluate boolean expressions, with appropriate short-circuiting.
 *
 *		The query planner reformulates clause expressions in the
 *		qualification to conjunctive normal form.  If we ever get
 *		an AND to evaluate, we can be sure that it's not a top-level
 *		clause in the qualification, but appears lower (as a function
 *		argument, for example), or in the target list.	Not that you
 *		need to know this, mind you...
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalNot(BoolExprState *notclause, ExprContext *econtext,
			bool *isNull, ExprDoneCond *isDone)
{
	ExprState  *clause = linitial(notclause->args);
	Datum		expr_value;

	expr_value = ExecEvalExpr(clause, econtext, isNull, isDone);

	/*
	 * if the expression evaluates to null, then we just cascade the null back
	 * to whoever called us.
	 */
	if (*isNull)
		return expr_value;

	/*
	 * evaluation of 'not' is simple.. expr is false, then return 'true' and
	 * vice versa.
	 */
	return BoolGetDatum(!DatumGetBool(expr_value));
}

/* ----------------------------------------------------------------
 *		ExecEvalOr
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalOr(BoolExprState *orExpr, ExprContext *econtext,
		   bool *isNull, ExprDoneCond *isDone)
{
	List	   *clauses = orExpr->args;
	ListCell   *clause;
	bool		AnyNull;

	if (isDone)
		*isDone = ExprSingleResult;

	AnyNull = false;

	/*
	 * If any of the clauses is TRUE, the OR result is TRUE regardless of the
	 * states of the rest of the clauses, so we can stop evaluating and return
	 * TRUE immediately.  If none are TRUE and one or more is NULL, we return
	 * NULL; otherwise we return FALSE.  This makes sense when you interpret
	 * NULL as "don't know": if we have a TRUE then the OR is TRUE even if we
	 * aren't sure about some of the other inputs. If all the known inputs are
	 * FALSE, but we have one or more "don't knows", then we have to report
	 * that we "don't know" what the OR's result should be --- perhaps one of
	 * the "don't knows" would have been TRUE if we'd known its value.  Only
	 * when all the inputs are known to be FALSE can we state confidently that
	 * the OR's result is FALSE.
	 */
	foreach(clause, clauses)
	{
		ExprState  *clausestate = (ExprState *) lfirst(clause);
		Datum		clause_value;

		clause_value = ExecEvalExpr(clausestate, econtext, isNull, NULL);

		/*
		 * if we have a non-null true result, then return it.
		 */
		if (*isNull)
			AnyNull = true;		/* remember we got a null */
		else if (DatumGetBool(clause_value))
			return clause_value;
	}

	/* AnyNull is true if at least one clause evaluated to NULL */
	*isNull = AnyNull;
	return BoolGetDatum(false);
}

/* ----------------------------------------------------------------
 *		ExecEvalAnd
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalAnd(BoolExprState *andExpr, ExprContext *econtext,
			bool *isNull, ExprDoneCond *isDone)
{
	List	   *clauses = andExpr->args;
	ListCell   *clause;
	bool		AnyNull;

	if (isDone)
		*isDone = ExprSingleResult;

	AnyNull = false;

	/*
	 * If any of the clauses is FALSE, the AND result is FALSE regardless of
	 * the states of the rest of the clauses, so we can stop evaluating and
	 * return FALSE immediately.  If none are FALSE and one or more is NULL,
	 * we return NULL; otherwise we return TRUE.  This makes sense when you
	 * interpret NULL as "don't know", using the same sort of reasoning as for
	 * OR, above.
	 */

	foreach(clause, clauses)
	{
		ExprState  *clausestate = (ExprState *) lfirst(clause);
		Datum		clause_value;

		clause_value = ExecEvalExpr(clausestate, econtext, isNull, NULL);

		/*
		 * if we have a non-null false result, then return it.
		 */
		if (*isNull)
			AnyNull = true;		/* remember we got a null */
		else if (!DatumGetBool(clause_value))
			return clause_value;
	}

	/* AnyNull is true if at least one clause evaluated to NULL */
	*isNull = AnyNull;
	return BoolGetDatum(!AnyNull);
}

/* ----------------------------------------------------------------
 *		ExecEvalConvertRowtype
 *
 *		Evaluate a rowtype coercion operation.	This may require
 *		rearranging field positions.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalConvertRowtype(ConvertRowtypeExprState *cstate,
					   ExprContext *econtext,
					   bool *isNull, ExprDoneCond *isDone)
{
	ConvertRowtypeExpr *convert = (ConvertRowtypeExpr *) cstate->xprstate.expr;
	HeapTuple	result;
	Datum		tupDatum;
	HeapTupleHeader tuple;
	HeapTupleData tmptup;

	tupDatum = ExecEvalExpr(cstate->arg, econtext, isNull, isDone);

	/* this test covers the isDone exception too: */
	if (*isNull)
		return tupDatum;

	tuple = DatumGetHeapTupleHeader(tupDatum);

	/* Lookup tupdescs if first time through or after rescan */
	if (cstate->indesc == NULL)
	{
		get_cached_rowtype(exprType((Node *) convert->arg), -1,
						   &cstate->indesc, econtext);
		cstate->initialized = false;
	}
	if (cstate->outdesc == NULL)
	{
		get_cached_rowtype(convert->resulttype, -1,
						   &cstate->outdesc, econtext);
		cstate->initialized = false;
	}

	Assert(HeapTupleHeaderGetTypeId(tuple) == cstate->indesc->tdtypeid);
	Assert(HeapTupleHeaderGetTypMod(tuple) == cstate->indesc->tdtypmod);

	/* if first time through, initialize conversion map */
	if (!cstate->initialized)
	{
		MemoryContext old_cxt;

		/* allocate map in long-lived memory context */
		old_cxt = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);

		/* prepare map from old to new attribute numbers */
		cstate->map = convert_tuples_by_name(cstate->indesc,
											 cstate->outdesc,
								 gettext_noop("could not convert row type"));
		cstate->initialized = true;

		MemoryContextSwitchTo(old_cxt);
	}

	/*
	 * No-op if no conversion needed (not clear this can happen here).
	 */
	if (cstate->map == NULL)
		return tupDatum;

	/*
	 * do_convert_tuple needs a HeapTuple not a bare HeapTupleHeader.
	 */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
	tmptup.t_data = tuple;

	result = do_convert_tuple(&tmptup, cstate->map);

	return HeapTupleGetDatum(result);
}

/* ----------------------------------------------------------------
 *		ExecEvalCase
 *
 *		Evaluate a CASE clause. Will have boolean expressions
 *		inside the WHEN clauses, and will have expressions
 *		for results.
 *		- thomas 1998-11-09
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalCase(CaseExprState *caseExpr, ExprContext *econtext,
			 bool *isNull, ExprDoneCond *isDone)
{
	List	   *clauses = caseExpr->args;
	ListCell   *clause;
	Datum		save_datum;
	bool		save_isNull;

	if (isDone)
		*isDone = ExprSingleResult;

	/*
	 * If there's a test expression, we have to evaluate it and save the value
	 * where the CaseTestExpr placeholders can find it. We must save and
	 * restore prior setting of econtext's caseValue fields, in case this node
	 * is itself within a larger CASE.
	 */
	save_datum = econtext->caseValue_datum;
	save_isNull = econtext->caseValue_isNull;

	if (caseExpr->arg)
	{
		econtext->caseValue_datum = ExecEvalExpr(caseExpr->arg,
												 econtext,
												 &econtext->caseValue_isNull,
												 NULL);
	}

	/*
	 * we evaluate each of the WHEN clauses in turn, as soon as one is true we
	 * return the corresponding result. If none are true then we return the
	 * value of the default clause, or NULL if there is none.
	 */
	foreach(clause, clauses)
	{
		CaseWhenState *wclause = lfirst(clause);
		Datum		clause_value;

		clause_value = ExecEvalExpr(wclause->expr,
									econtext,
									isNull,
									NULL);

		/*
		 * if we have a true test, then we return the result, since the case
		 * statement is satisfied.	A NULL result from the test is not
		 * considered true.
		 */
		if (DatumGetBool(clause_value) && !*isNull)
		{
			econtext->caseValue_datum = save_datum;
			econtext->caseValue_isNull = save_isNull;
			return ExecEvalExpr(wclause->result,
								econtext,
								isNull,
								isDone);
		}
	}

	econtext->caseValue_datum = save_datum;
	econtext->caseValue_isNull = save_isNull;

	if (caseExpr->defresult)
	{
		return ExecEvalExpr(caseExpr->defresult,
							econtext,
							isNull,
							isDone);
	}

	*isNull = true;
	return (Datum) 0;
}

/*
 * ExecEvalCaseTestExpr
 *
 * Return the value stored by CASE.
 */
static Datum
ExecEvalCaseTestExpr(ExprState *exprstate,
					 ExprContext *econtext,
					 bool *isNull, ExprDoneCond *isDone)
{
	if (isDone)
		*isDone = ExprSingleResult;
	*isNull = econtext->caseValue_isNull;
	return econtext->caseValue_datum;
}

/* ----------------------------------------------------------------
 *		ExecEvalArray - ARRAY[] expressions
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalArray(ArrayExprState *astate, ExprContext *econtext,
			  bool *isNull, ExprDoneCond *isDone)
{
	ArrayExpr  *arrayExpr = (ArrayExpr *) astate->xprstate.expr;
	ArrayType  *result;
	ListCell   *element;
	Oid			element_type = arrayExpr->element_typeid;
	int			ndims = 0;
	int			dims[MAXDIM];
	int			lbs[MAXDIM];

	/* Set default values for result flags: non-null, not a set result */
	*isNull = false;
	if (isDone)
		*isDone = ExprSingleResult;

	if (!arrayExpr->multidims)
	{
		/* Elements are presumably of scalar type */
		int			nelems;
		Datum	   *dvalues;
		bool	   *dnulls;
		int			i = 0;

		ndims = 1;
		nelems = list_length(astate->elements);

		/* Shouldn't happen here, but if length is 0, return empty array */
		if (nelems == 0)
			return PointerGetDatum(construct_empty_array(element_type));

		dvalues = (Datum *) palloc(nelems * sizeof(Datum));
		dnulls = (bool *) palloc(nelems * sizeof(bool));

		/* loop through and build array of datums */
		foreach(element, astate->elements)
		{
			ExprState  *e = (ExprState *) lfirst(element);

			dvalues[i] = ExecEvalExpr(e, econtext, &dnulls[i], NULL);
			i++;
		}

		/* setup for 1-D array of the given length */
		dims[0] = nelems;
		lbs[0] = 1;

		result = construct_md_array(dvalues, dnulls, ndims, dims, lbs,
									element_type,
									astate->elemlength,
									astate->elembyval,
									astate->elemalign);
	}
	else
	{
		/* Must be nested array expressions */
		int			nbytes = 0;
		int			nitems = 0;
		int			outer_nelems = 0;
		int			elem_ndims = 0;
		int		   *elem_dims = NULL;
		int		   *elem_lbs = NULL;
		bool		firstone = true;
		bool		havenulls = false;
		bool		haveempty = false;
		char	  **subdata;
		bits8	  **subbitmaps;
		int		   *subbytes;
		int		   *subnitems;
		int			i;
		int32		dataoffset;
		char	   *dat;
		int			iitem;

		i = list_length(astate->elements);
		subdata = (char **) palloc(i * sizeof(char *));
		subbitmaps = (bits8 **) palloc(i * sizeof(bits8 *));
		subbytes = (int *) palloc(i * sizeof(int));
		subnitems = (int *) palloc(i * sizeof(int));

		/* loop through and get data area from each element */
		foreach(element, astate->elements)
		{
			ExprState  *e = (ExprState *) lfirst(element);
			bool		eisnull;
			Datum		arraydatum;
			ArrayType  *array;
			int			this_ndims;

			arraydatum = ExecEvalExpr(e, econtext, &eisnull, NULL);
			/* temporarily ignore null subarrays */
			if (eisnull)
			{
				haveempty = true;
				continue;
			}

			array = DatumGetArrayTypeP(arraydatum);

			/* run-time double-check on element type */
			if (element_type != ARR_ELEMTYPE(array))
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("cannot merge incompatible arrays"),
						 errdetail("Array with element type %s cannot be "
						 "included in ARRAY construct with element type %s.",
								   format_type_be(ARR_ELEMTYPE(array)),
								   format_type_be(element_type))));

			this_ndims = ARR_NDIM(array);
			/* temporarily ignore zero-dimensional subarrays */
			if (this_ndims <= 0)
			{
				haveempty = true;
				continue;
			}

			if (firstone)
			{
				/* Get sub-array details from first member */
				elem_ndims = this_ndims;
				ndims = elem_ndims + 1;
				if (ndims <= 0 || ndims > MAXDIM)
					ereport(ERROR,
							(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
						  errmsg("number of array dimensions (%d) exceeds " \
								 "the maximum allowed (%d)", ndims, MAXDIM)));

				elem_dims = (int *) palloc(elem_ndims * sizeof(int));
				memcpy(elem_dims, ARR_DIMS(array), elem_ndims * sizeof(int));
				elem_lbs = (int *) palloc(elem_ndims * sizeof(int));
				memcpy(elem_lbs, ARR_LBOUND(array), elem_ndims * sizeof(int));

				firstone = false;
			}
			else
			{
				/* Check other sub-arrays are compatible */
				if (elem_ndims != this_ndims ||
					memcmp(elem_dims, ARR_DIMS(array),
						   elem_ndims * sizeof(int)) != 0 ||
					memcmp(elem_lbs, ARR_LBOUND(array),
						   elem_ndims * sizeof(int)) != 0)
					ereport(ERROR,
							(errcode(ERRCODE_ARRAY_SUBSCRIPT_ERROR),
							 errmsg("multidimensional arrays must have array "
									"expressions with matching dimensions")));
			}

			subdata[outer_nelems] = ARR_DATA_PTR(array);
			subbitmaps[outer_nelems] = ARR_NULLBITMAP(array);
			subbytes[outer_nelems] = ARR_SIZE(array) - ARR_DATA_OFFSET(array);
			nbytes += subbytes[outer_nelems];
			subnitems[outer_nelems] = ArrayGetNItems(this_ndims,
													 ARR_DIMS(array));
			nitems += subnitems[outer_nelems];
			havenulls |= ARR_HASNULL(array);
			outer_nelems++;
		}

		/*
		 * If all items were null or empty arrays, return an empty array;
		 * otherwise, if some were and some weren't, raise error.  (Note: we
		 * must special-case this somehow to avoid trying to generate a 1-D
		 * array formed from empty arrays.	It's not ideal...)
		 */
		if (haveempty)
		{
			if (ndims == 0)		/* didn't find any nonempty array */
				return PointerGetDatum(construct_empty_array(element_type));
			ereport(ERROR,
					(errcode(ERRCODE_ARRAY_SUBSCRIPT_ERROR),
					 errmsg("multidimensional arrays must have array "
							"expressions with matching dimensions")));
		}

		/* setup for multi-D array */
		dims[0] = outer_nelems;
		lbs[0] = 1;
		for (i = 1; i < ndims; i++)
		{
			dims[i] = elem_dims[i - 1];
			lbs[i] = elem_lbs[i - 1];
		}

		if (havenulls)
		{
			dataoffset = ARR_OVERHEAD_WITHNULLS(ndims, nitems);
			nbytes += dataoffset;
		}
		else
		{
			dataoffset = 0;		/* marker for no null bitmap */
			nbytes += ARR_OVERHEAD_NONULLS(ndims);
		}

		result = (ArrayType *) palloc(nbytes);
		SET_VARSIZE(result, nbytes);
		result->ndim = ndims;
		result->dataoffset = dataoffset;
		result->elemtype = element_type;
		memcpy(ARR_DIMS(result), dims, ndims * sizeof(int));
		memcpy(ARR_LBOUND(result), lbs, ndims * sizeof(int));

		dat = ARR_DATA_PTR(result);
		iitem = 0;
		for (i = 0; i < outer_nelems; i++)
		{
			memcpy(dat, subdata[i], subbytes[i]);
			dat += subbytes[i];
			if (havenulls)
				array_bitmap_copy(ARR_NULLBITMAP(result), iitem,
								  subbitmaps[i], 0,
								  subnitems[i]);
			iitem += subnitems[i];
		}
	}

	return PointerGetDatum(result);
}

/* ----------------------------------------------------------------
 *		ExecEvalRow - ROW() expressions
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalRow(RowExprState *rstate,
			ExprContext *econtext,
			bool *isNull, ExprDoneCond *isDone)
{
	HeapTuple	tuple;
	Datum	   *values;
	bool	   *isnull;
	int			natts;
	ListCell   *arg;
	int			i;

	/* Set default values for result flags: non-null, not a set result */
	*isNull = false;
	if (isDone)
		*isDone = ExprSingleResult;

	/* Allocate workspace */
	natts = rstate->tupdesc->natts;
	values = (Datum *) palloc0(natts * sizeof(Datum));
	isnull = (bool *) palloc(natts * sizeof(bool));

	/* preset to nulls in case rowtype has some later-added columns */
	memset(isnull, true, natts * sizeof(bool));

	/* Evaluate field values */
	i = 0;
	foreach(arg, rstate->args)
	{
		ExprState  *e = (ExprState *) lfirst(arg);

		values[i] = ExecEvalExpr(e, econtext, &isnull[i], NULL);
		i++;
	}

	tuple = heap_form_tuple(rstate->tupdesc, values, isnull);

	pfree(values);
	pfree(isnull);

	return HeapTupleGetDatum(tuple);
}

/* ----------------------------------------------------------------
 *		ExecEvalRowCompare - ROW() comparison-op ROW()
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalRowCompare(RowCompareExprState *rstate,
				   ExprContext *econtext,
				   bool *isNull, ExprDoneCond *isDone)
{
	bool		result;
	RowCompareType rctype = ((RowCompareExpr *) rstate->xprstate.expr)->rctype;
	int32		cmpresult = 0;
	ListCell   *l;
	ListCell   *r;
	int			i;

	if (isDone)
		*isDone = ExprSingleResult;
	*isNull = true;				/* until we get a result */

	i = 0;
	forboth(l, rstate->largs, r, rstate->rargs)
	{
		ExprState  *le = (ExprState *) lfirst(l);
		ExprState  *re = (ExprState *) lfirst(r);
		FunctionCallInfoData locfcinfo;

		InitFunctionCallInfoData(locfcinfo, &(rstate->funcs[i]), 2,
								 rstate->collations[i],
								 NULL, NULL);
		locfcinfo.arg[0] = ExecEvalExpr(le, econtext,
										&locfcinfo.argnull[0], NULL);
		locfcinfo.arg[1] = ExecEvalExpr(re, econtext,
										&locfcinfo.argnull[1], NULL);
		if (rstate->funcs[i].fn_strict &&
			(locfcinfo.argnull[0] || locfcinfo.argnull[1]))
			return (Datum) 0;	/* force NULL result */
		locfcinfo.isnull = false;
		cmpresult = DatumGetInt32(FunctionCallInvoke(&locfcinfo));
		if (locfcinfo.isnull)
			return (Datum) 0;	/* force NULL result */
		if (cmpresult != 0)
			break;				/* no need to compare remaining columns */
		i++;
	}

	switch (rctype)
	{
			/* EQ and NE cases aren't allowed here */
		case ROWCOMPARE_LT:
			result = (cmpresult < 0);
			break;
		case ROWCOMPARE_LE:
			result = (cmpresult <= 0);
			break;
		case ROWCOMPARE_GE:
			result = (cmpresult >= 0);
			break;
		case ROWCOMPARE_GT:
			result = (cmpresult > 0);
			break;
		default:
			elog(ERROR, "unrecognized RowCompareType: %d", (int) rctype);
			result = 0;			/* keep compiler quiet */
			break;
	}

	*isNull = false;
	return BoolGetDatum(result);
}

/* ----------------------------------------------------------------
 *		ExecEvalCoalesce
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalCoalesce(CoalesceExprState *coalesceExpr, ExprContext *econtext,
				 bool *isNull, ExprDoneCond *isDone)
{
	ListCell   *arg;

	if (isDone)
		*isDone = ExprSingleResult;

	/* Simply loop through until something NOT NULL is found */
	foreach(arg, coalesceExpr->args)
	{
		ExprState  *e = (ExprState *) lfirst(arg);
		Datum		value;

		value = ExecEvalExpr(e, econtext, isNull, NULL);
		if (!*isNull)
			return value;
	}

	/* Else return NULL */
	*isNull = true;
	return (Datum) 0;
}

/* ----------------------------------------------------------------
 *		ExecEvalMinMax
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalMinMax(MinMaxExprState *minmaxExpr, ExprContext *econtext,
			   bool *isNull, ExprDoneCond *isDone)
{
	Datum		result = (Datum) 0;
	MinMaxExpr *minmax = (MinMaxExpr *) minmaxExpr->xprstate.expr;
	Oid			collation = minmax->inputcollid;
	MinMaxOp	op = minmax->op;
	FunctionCallInfoData locfcinfo;
	ListCell   *arg;

	if (isDone)
		*isDone = ExprSingleResult;
	*isNull = true;				/* until we get a result */

	InitFunctionCallInfoData(locfcinfo, &minmaxExpr->cfunc, 2,
							 collation, NULL, NULL);
	locfcinfo.argnull[0] = false;
	locfcinfo.argnull[1] = false;

	foreach(arg, minmaxExpr->args)
	{
		ExprState  *e = (ExprState *) lfirst(arg);
		Datum		value;
		bool		valueIsNull;
		int32		cmpresult;

		value = ExecEvalExpr(e, econtext, &valueIsNull, NULL);
		if (valueIsNull)
			continue;			/* ignore NULL inputs */

		if (*isNull)
		{
			/* first nonnull input, adopt value */
			result = value;
			*isNull = false;
		}
		else
		{
			/* apply comparison function */
			locfcinfo.arg[0] = result;
			locfcinfo.arg[1] = value;
			locfcinfo.isnull = false;
			cmpresult = DatumGetInt32(FunctionCallInvoke(&locfcinfo));
			if (locfcinfo.isnull)		/* probably should not happen */
				continue;
			if (cmpresult > 0 && op == IS_LEAST)
				result = value;
			else if (cmpresult < 0 && op == IS_GREATEST)
				result = value;
		}
	}

	return result;
}

/* ----------------------------------------------------------------
 *		ExecEvalXml
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalXml(XmlExprState *xmlExpr, ExprContext *econtext,
			bool *isNull, ExprDoneCond *isDone)
{
	XmlExpr    *xexpr = (XmlExpr *) xmlExpr->xprstate.expr;
	Datum		value;
	bool		isnull;
	ListCell   *arg;
	ListCell   *narg;

	if (isDone)
		*isDone = ExprSingleResult;
	*isNull = true;				/* until we get a result */

	switch (xexpr->op)
	{
		case IS_XMLCONCAT:
			{
				List	   *values = NIL;

				foreach(arg, xmlExpr->args)
				{
					ExprState  *e = (ExprState *) lfirst(arg);

					value = ExecEvalExpr(e, econtext, &isnull, NULL);
					if (!isnull)
						values = lappend(values, DatumGetPointer(value));
				}

				if (list_length(values) > 0)
				{
					*isNull = false;
					return PointerGetDatum(xmlconcat(values));
				}
				else
					return (Datum) 0;
			}
			break;

		case IS_XMLFOREST:
			{
				StringInfoData buf;

				initStringInfo(&buf);
				forboth(arg, xmlExpr->named_args, narg, xexpr->arg_names)
				{
					ExprState  *e = (ExprState *) lfirst(arg);
					char	   *argname = strVal(lfirst(narg));

					value = ExecEvalExpr(e, econtext, &isnull, NULL);
					if (!isnull)
					{
						appendStringInfo(&buf, "<%s>%s</%s>",
										 argname,
										 map_sql_value_to_xml_value(value, exprType((Node *) e->expr), true),
										 argname);
						*isNull = false;
					}
				}

				if (*isNull)
				{
					pfree(buf.data);
					return (Datum) 0;
				}
				else
				{
					text	   *result;

					result = cstring_to_text_with_len(buf.data, buf.len);
					pfree(buf.data);

					return PointerGetDatum(result);
				}
			}
			break;

		case IS_XMLELEMENT:
			*isNull = false;
			return PointerGetDatum(xmlelement(xmlExpr, econtext));
			break;

		case IS_XMLPARSE:
			{
				ExprState  *e;
				text	   *data;
				bool		preserve_whitespace;

				/* arguments are known to be text, bool */
				Assert(list_length(xmlExpr->args) == 2);

				e = (ExprState *) linitial(xmlExpr->args);
				value = ExecEvalExpr(e, econtext, &isnull, NULL);
				if (isnull)
					return (Datum) 0;
				data = DatumGetTextP(value);

				e = (ExprState *) lsecond(xmlExpr->args);
				value = ExecEvalExpr(e, econtext, &isnull, NULL);
				if (isnull)		/* probably can't happen */
					return (Datum) 0;
				preserve_whitespace = DatumGetBool(value);

				*isNull = false;

				return PointerGetDatum(xmlparse(data,
												xexpr->xmloption,
												preserve_whitespace));
			}
			break;

		case IS_XMLPI:
			{
				ExprState  *e;
				text	   *arg;

				/* optional argument is known to be text */
				Assert(list_length(xmlExpr->args) <= 1);

				if (xmlExpr->args)
				{
					e = (ExprState *) linitial(xmlExpr->args);
					value = ExecEvalExpr(e, econtext, &isnull, NULL);
					if (isnull)
						arg = NULL;
					else
						arg = DatumGetTextP(value);
				}
				else
				{
					arg = NULL;
					isnull = false;
				}

				return PointerGetDatum(xmlpi(xexpr->name, arg, isnull, isNull));
			}
			break;

		case IS_XMLROOT:
			{
				ExprState  *e;
				xmltype    *data;
				text	   *version;
				int			standalone;

				/* arguments are known to be xml, text, int */
				Assert(list_length(xmlExpr->args) == 3);

				e = (ExprState *) linitial(xmlExpr->args);
				value = ExecEvalExpr(e, econtext, &isnull, NULL);
				if (isnull)
					return (Datum) 0;
				data = DatumGetXmlP(value);

				e = (ExprState *) lsecond(xmlExpr->args);
				value = ExecEvalExpr(e, econtext, &isnull, NULL);
				if (isnull)
					version = NULL;
				else
					version = DatumGetTextP(value);

				e = (ExprState *) lthird(xmlExpr->args);
				value = ExecEvalExpr(e, econtext, &isnull, NULL);
				standalone = DatumGetInt32(value);

				*isNull = false;

				return PointerGetDatum(xmlroot(data,
											   version,
											   standalone));
			}
			break;

		case IS_XMLSERIALIZE:
			{
				ExprState  *e;

				/* argument type is known to be xml */
				Assert(list_length(xmlExpr->args) == 1);

				e = (ExprState *) linitial(xmlExpr->args);
				value = ExecEvalExpr(e, econtext, &isnull, NULL);
				if (isnull)
					return (Datum) 0;

				*isNull = false;

				return PointerGetDatum(xmltotext_with_xmloption(DatumGetXmlP(value), xexpr->xmloption));
			}
			break;

		case IS_DOCUMENT:
			{
				ExprState  *e;

				/* optional argument is known to be xml */
				Assert(list_length(xmlExpr->args) == 1);

				e = (ExprState *) linitial(xmlExpr->args);
				value = ExecEvalExpr(e, econtext, &isnull, NULL);
				if (isnull)
					return (Datum) 0;
				else
				{
					*isNull = false;
					return BoolGetDatum(xml_is_document(DatumGetXmlP(value)));
				}
			}
			break;
	}

	elog(ERROR, "unrecognized XML operation");
	return (Datum) 0;
}

/* ----------------------------------------------------------------
 *		ExecEvalNullIf
 *
 * Note that this is *always* derived from the equals operator,
 * but since we need special processing of the arguments
 * we can not simply reuse ExecEvalOper() or ExecEvalFunc().
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalNullIf(FuncExprState *nullIfExpr,
			   ExprContext *econtext,
			   bool *isNull, ExprDoneCond *isDone)
{
	Datum		result;
	FunctionCallInfo fcinfo;
	ExprDoneCond argDone;

	if (isDone)
		*isDone = ExprSingleResult;

	/*
	 * Initialize function cache if first time through
	 */
	if (nullIfExpr->func.fn_oid == InvalidOid)
	{
		NullIfExpr *op = (NullIfExpr *) nullIfExpr->xprstate.expr;

		init_fcache(op->opfuncid, op->inputcollid, nullIfExpr, econtext);
		Assert(!nullIfExpr->func.fn_retset);
	}

	/*
	 * Evaluate arguments
	 */
	fcinfo = &nullIfExpr->fcinfo_data;
	argDone = ExecEvalFuncArgs(fcinfo, nullIfExpr->args, econtext);
	if (argDone != ExprSingleResult)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("NULLIF does not support set arguments")));
	Assert(fcinfo->nargs == 2);

	/* if either argument is NULL they can't be equal */
	if (!fcinfo->argnull[0] && !fcinfo->argnull[1])
	{
		fcinfo->isnull = false;
		result = FunctionCallInvoke(fcinfo);
		/* if the arguments are equal return null */
		if (!fcinfo->isnull && DatumGetBool(result))
		{
			*isNull = true;
			return (Datum) 0;
		}
	}

	/* else return first argument */
	*isNull = fcinfo->argnull[0];
	return fcinfo->arg[0];
}

/* ----------------------------------------------------------------
 *		ExecEvalNullTest
 *
 *		Evaluate a NullTest node.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalNullTest(NullTestState *nstate,
				 ExprContext *econtext,
				 bool *isNull,
				 ExprDoneCond *isDone)
{
	NullTest   *ntest = (NullTest *) nstate->xprstate.expr;
	Datum		result;

	result = ExecEvalExpr(nstate->arg, econtext, isNull, isDone);

	if (isDone && *isDone == ExprEndResult)
		return result;			/* nothing to check */

	if (ntest->argisrow && !(*isNull))
	{
		HeapTupleHeader tuple;
		Oid			tupType;
		int32		tupTypmod;
		TupleDesc	tupDesc;
		HeapTupleData tmptup;
		int			att;

		tuple = DatumGetHeapTupleHeader(result);

		tupType = HeapTupleHeaderGetTypeId(tuple);
		tupTypmod = HeapTupleHeaderGetTypMod(tuple);

		/* Lookup tupdesc if first time through or if type changes */
		tupDesc = get_cached_rowtype(tupType, tupTypmod,
									 &nstate->argdesc, econtext);

		/*
		 * heap_attisnull needs a HeapTuple not a bare HeapTupleHeader.
		 */
		tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
		tmptup.t_data = tuple;

		for (att = 1; att <= tupDesc->natts; att++)
		{
			/* ignore dropped columns */
			if (tupDesc->attrs[att - 1]->attisdropped)
				continue;
			if (heap_attisnull(&tmptup, att))
			{
				/* null field disproves IS NOT NULL */
				if (ntest->nulltesttype == IS_NOT_NULL)
					return BoolGetDatum(false);
			}
			else
			{
				/* non-null field disproves IS NULL */
				if (ntest->nulltesttype == IS_NULL)
					return BoolGetDatum(false);
			}
		}

		return BoolGetDatum(true);
	}
	else
	{
		/* Simple scalar-argument case, or a null rowtype datum */
		switch (ntest->nulltesttype)
		{
			case IS_NULL:
				if (*isNull)
				{
					*isNull = false;
					return BoolGetDatum(true);
				}
				else
					return BoolGetDatum(false);
			case IS_NOT_NULL:
				if (*isNull)
				{
					*isNull = false;
					return BoolGetDatum(false);
				}
				else
					return BoolGetDatum(true);
			default:
				elog(ERROR, "unrecognized nulltesttype: %d",
					 (int) ntest->nulltesttype);
				return (Datum) 0;		/* keep compiler quiet */
		}
	}
}

/* ----------------------------------------------------------------
 *		ExecEvalBooleanTest
 *
 *		Evaluate a BooleanTest node.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalBooleanTest(GenericExprState *bstate,
					ExprContext *econtext,
					bool *isNull,
					ExprDoneCond *isDone)
{
	BooleanTest *btest = (BooleanTest *) bstate->xprstate.expr;
	Datum		result;

	result = ExecEvalExpr(bstate->arg, econtext, isNull, isDone);

	if (isDone && *isDone == ExprEndResult)
		return result;			/* nothing to check */

	switch (btest->booltesttype)
	{
		case IS_TRUE:
			if (*isNull)
			{
				*isNull = false;
				return BoolGetDatum(false);
			}
			else if (DatumGetBool(result))
				return BoolGetDatum(true);
			else
				return BoolGetDatum(false);
		case IS_NOT_TRUE:
			if (*isNull)
			{
				*isNull = false;
				return BoolGetDatum(true);
			}
			else if (DatumGetBool(result))
				return BoolGetDatum(false);
			else
				return BoolGetDatum(true);
		case IS_FALSE:
			if (*isNull)
			{
				*isNull = false;
				return BoolGetDatum(false);
			}
			else if (DatumGetBool(result))
				return BoolGetDatum(false);
			else
				return BoolGetDatum(true);
		case IS_NOT_FALSE:
			if (*isNull)
			{
				*isNull = false;
				return BoolGetDatum(true);
			}
			else if (DatumGetBool(result))
				return BoolGetDatum(true);
			else
				return BoolGetDatum(false);
		case IS_UNKNOWN:
			if (*isNull)
			{
				*isNull = false;
				return BoolGetDatum(true);
			}
			else
				return BoolGetDatum(false);
		case IS_NOT_UNKNOWN:
			if (*isNull)
			{
				*isNull = false;
				return BoolGetDatum(false);
			}
			else
				return BoolGetDatum(true);
		default:
			elog(ERROR, "unrecognized booltesttype: %d",
				 (int) btest->booltesttype);
			return (Datum) 0;	/* keep compiler quiet */
	}
}

/*
 * ExecEvalCoerceToDomain
 *
 * Test the provided data against the domain constraint(s).  If the data
 * passes the constraint specifications, pass it through (return the
 * datum) otherwise throw an error.
 */
static Datum
ExecEvalCoerceToDomain(CoerceToDomainState *cstate, ExprContext *econtext,
					   bool *isNull, ExprDoneCond *isDone)
{
	CoerceToDomain *ctest = (CoerceToDomain *) cstate->xprstate.expr;
	Datum		result;
	ListCell   *l;

	result = ExecEvalExpr(cstate->arg, econtext, isNull, isDone);

	if (isDone && *isDone == ExprEndResult)
		return result;			/* nothing to check */

	foreach(l, cstate->constraints)
	{
		DomainConstraintState *con = (DomainConstraintState *) lfirst(l);

		switch (con->constrainttype)
		{
			case DOM_CONSTRAINT_NOTNULL:
				if (*isNull)
					ereport(ERROR,
							(errcode(ERRCODE_NOT_NULL_VIOLATION),
							 errmsg("domain %s does not allow null values",
									format_type_be(ctest->resulttype))));
				break;
			case DOM_CONSTRAINT_CHECK:
				{
					Datum		conResult;
					bool		conIsNull;
					Datum		save_datum;
					bool		save_isNull;

					/*
					 * Set up value to be returned by CoerceToDomainValue
					 * nodes. We must save and restore prior setting of
					 * econtext's domainValue fields, in case this node is
					 * itself within a check expression for another domain.
					 */
					save_datum = econtext->domainValue_datum;
					save_isNull = econtext->domainValue_isNull;

					econtext->domainValue_datum = result;
					econtext->domainValue_isNull = *isNull;

					conResult = ExecEvalExpr(con->check_expr,
											 econtext, &conIsNull, NULL);

					if (!conIsNull &&
						!DatumGetBool(conResult))
						ereport(ERROR,
								(errcode(ERRCODE_CHECK_VIOLATION),
								 errmsg("value for domain %s violates check constraint \"%s\"",
										format_type_be(ctest->resulttype),
										con->name)));
					econtext->domainValue_datum = save_datum;
					econtext->domainValue_isNull = save_isNull;

					break;
				}
			default:
				elog(ERROR, "unrecognized constraint type: %d",
					 (int) con->constrainttype);
				break;
		}
	}

	/* If all has gone well (constraints did not fail) return the datum */
	return result;
}

/*
 * ExecEvalCoerceToDomainValue
 *
 * Return the value stored by CoerceToDomain.
 */
static Datum
ExecEvalCoerceToDomainValue(ExprState *exprstate,
							ExprContext *econtext,
							bool *isNull, ExprDoneCond *isDone)
{
	if (isDone)
		*isDone = ExprSingleResult;
	*isNull = econtext->domainValue_isNull;
	return econtext->domainValue_datum;
}

/* ----------------------------------------------------------------
 *		ExecEvalFieldSelect
 *
 *		Evaluate a FieldSelect node.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalFieldSelect(FieldSelectState *fstate,
					ExprContext *econtext,
					bool *isNull,
					ExprDoneCond *isDone)
{
	FieldSelect *fselect = (FieldSelect *) fstate->xprstate.expr;
	AttrNumber	fieldnum = fselect->fieldnum;
	Datum		result;
	Datum		tupDatum;
	HeapTupleHeader tuple;
	Oid			tupType;
	int32		tupTypmod;
	TupleDesc	tupDesc;
	Form_pg_attribute attr;
	HeapTupleData tmptup;

	tupDatum = ExecEvalExpr(fstate->arg, econtext, isNull, isDone);

	/* this test covers the isDone exception too: */
	if (*isNull)
		return tupDatum;

	tuple = DatumGetHeapTupleHeader(tupDatum);

	tupType = HeapTupleHeaderGetTypeId(tuple);
	tupTypmod = HeapTupleHeaderGetTypMod(tuple);

	/* Lookup tupdesc if first time through or if type changes */
	tupDesc = get_cached_rowtype(tupType, tupTypmod,
								 &fstate->argdesc, econtext);

	/*
	 * Find field's attr record.  Note we don't support system columns here: a
	 * datum tuple doesn't have valid values for most of the interesting
	 * system columns anyway.
	 */
	if (fieldnum <= 0)			/* should never happen */
		elog(ERROR, "unsupported reference to system column %d in FieldSelect",
			 fieldnum);
	if (fieldnum > tupDesc->natts)		/* should never happen */
		elog(ERROR, "attribute number %d exceeds number of columns %d",
			 fieldnum, tupDesc->natts);
	attr = tupDesc->attrs[fieldnum - 1];

	/* Check for dropped column, and force a NULL result if so */
	if (attr->attisdropped)
	{
		*isNull = true;
		return (Datum) 0;
	}

	/* Check for type mismatch --- possible after ALTER COLUMN TYPE? */
	/* As in ExecEvalScalarVar, we should but can't check typmod */
	if (fselect->resulttype != attr->atttypid)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("attribute %d has wrong type", fieldnum),
				 errdetail("Table has type %s, but query expects %s.",
						   format_type_be(attr->atttypid),
						   format_type_be(fselect->resulttype))));

	/* heap_getattr needs a HeapTuple not a bare HeapTupleHeader */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
	tmptup.t_data = tuple;

	result = heap_getattr(&tmptup,
						  fieldnum,
						  tupDesc,
						  isNull);
	return result;
}

/* ----------------------------------------------------------------
 *		ExecEvalFieldStore
 *
 *		Evaluate a FieldStore node.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalFieldStore(FieldStoreState *fstate,
				   ExprContext *econtext,
				   bool *isNull,
				   ExprDoneCond *isDone)
{
	FieldStore *fstore = (FieldStore *) fstate->xprstate.expr;
	HeapTuple	tuple;
	Datum		tupDatum;
	TupleDesc	tupDesc;
	Datum	   *values;
	bool	   *isnull;
	Datum		save_datum;
	bool		save_isNull;
	ListCell   *l1,
			   *l2;

	tupDatum = ExecEvalExpr(fstate->arg, econtext, isNull, isDone);

	if (isDone && *isDone == ExprEndResult)
		return tupDatum;

	/* Lookup tupdesc if first time through or after rescan */
	tupDesc = get_cached_rowtype(fstore->resulttype, -1,
								 &fstate->argdesc, econtext);

	/* Allocate workspace */
	values = (Datum *) palloc(tupDesc->natts * sizeof(Datum));
	isnull = (bool *) palloc(tupDesc->natts * sizeof(bool));

	if (!*isNull)
	{
		/*
		 * heap_deform_tuple needs a HeapTuple not a bare HeapTupleHeader. We
		 * set all the fields in the struct just in case.
		 */
		HeapTupleHeader tuphdr;
		HeapTupleData tmptup;

		tuphdr = DatumGetHeapTupleHeader(tupDatum);
		tmptup.t_len = HeapTupleHeaderGetDatumLength(tuphdr);
		ItemPointerSetInvalid(&(tmptup.t_self));
		tmptup.t_tableOid = InvalidOid;
		tmptup.t_data = tuphdr;

		heap_deform_tuple(&tmptup, tupDesc, values, isnull);
	}
	else
	{
		/* Convert null input tuple into an all-nulls row */
		memset(isnull, true, tupDesc->natts * sizeof(bool));
	}

	/* Result is never null */
	*isNull = false;

	save_datum = econtext->caseValue_datum;
	save_isNull = econtext->caseValue_isNull;

	forboth(l1, fstate->newvals, l2, fstore->fieldnums)
	{
		ExprState  *newval = (ExprState *) lfirst(l1);
		AttrNumber	fieldnum = lfirst_int(l2);

		Assert(fieldnum > 0 && fieldnum <= tupDesc->natts);

		/*
		 * Use the CaseTestExpr mechanism to pass down the old value of the
		 * field being replaced; this is needed in case the newval is itself a
		 * FieldStore or ArrayRef that has to obtain and modify the old value.
		 * It's safe to reuse the CASE mechanism because there cannot be a
		 * CASE between here and where the value would be needed, and a field
		 * assignment can't be within a CASE either.  (So saving and restoring
		 * the caseValue is just paranoia, but let's do it anyway.)
		 */
		econtext->caseValue_datum = values[fieldnum - 1];
		econtext->caseValue_isNull = isnull[fieldnum - 1];

		values[fieldnum - 1] = ExecEvalExpr(newval,
											econtext,
											&isnull[fieldnum - 1],
											NULL);
	}

	econtext->caseValue_datum = save_datum;
	econtext->caseValue_isNull = save_isNull;

	tuple = heap_form_tuple(tupDesc, values, isnull);

	pfree(values);
	pfree(isnull);

	return HeapTupleGetDatum(tuple);
}

/* ----------------------------------------------------------------
 *		ExecEvalRelabelType
 *
 *		Evaluate a RelabelType node.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalRelabelType(GenericExprState *exprstate,
					ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone)
{
	return ExecEvalExpr(exprstate->arg, econtext, isNull, isDone);
}

/* ----------------------------------------------------------------
 *		ExecEvalCoerceViaIO
 *
 *		Evaluate a CoerceViaIO node.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalCoerceViaIO(CoerceViaIOState *iostate,
					ExprContext *econtext,
					bool *isNull, ExprDoneCond *isDone)
{
	Datum		result;
	Datum		inputval;
	char	   *string;

	inputval = ExecEvalExpr(iostate->arg, econtext, isNull, isDone);

	if (isDone && *isDone == ExprEndResult)
		return inputval;		/* nothing to do */

	if (*isNull)
		string = NULL;			/* output functions are not called on nulls */
	else
		string = OutputFunctionCall(&iostate->outfunc, inputval);

	result = InputFunctionCall(&iostate->infunc,
							   string,
							   iostate->intypioparam,
							   -1);

	/* The input function cannot change the null/not-null status */
	return result;
}

/* ----------------------------------------------------------------
 *		ExecEvalArrayCoerceExpr
 *
 *		Evaluate an ArrayCoerceExpr node.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalArrayCoerceExpr(ArrayCoerceExprState *astate,
						ExprContext *econtext,
						bool *isNull, ExprDoneCond *isDone)
{
	ArrayCoerceExpr *acoerce = (ArrayCoerceExpr *) astate->xprstate.expr;
	Datum		result;
	ArrayType  *array;
	FunctionCallInfoData locfcinfo;

	result = ExecEvalExpr(astate->arg, econtext, isNull, isDone);

	if (isDone && *isDone == ExprEndResult)
		return result;			/* nothing to do */
	if (*isNull)
		return result;			/* nothing to do */

	/*
	 * If it's binary-compatible, modify the element type in the array header,
	 * but otherwise leave the array as we received it.
	 */
	if (!OidIsValid(acoerce->elemfuncid))
	{
		/* Detoast input array if necessary, and copy in any case */
		array = DatumGetArrayTypePCopy(result);
		ARR_ELEMTYPE(array) = astate->resultelemtype;
		PG_RETURN_ARRAYTYPE_P(array);
	}

	/* Detoast input array if necessary, but don't make a useless copy */
	array = DatumGetArrayTypeP(result);

	/* Initialize function cache if first time through */
	if (astate->elemfunc.fn_oid == InvalidOid)
	{
		AclResult	aclresult;

		/* Check permission to call function */
		aclresult = pg_proc_aclcheck(acoerce->elemfuncid, GetUserId(),
									 ACL_EXECUTE);
		if (aclresult != ACLCHECK_OK)
			aclcheck_error(aclresult, ACL_KIND_PROC,
						   get_func_name(acoerce->elemfuncid));

		/* Set up the primary fmgr lookup information */
		fmgr_info_cxt(acoerce->elemfuncid, &(astate->elemfunc),
					  econtext->ecxt_per_query_memory);
		fmgr_info_set_expr((Node *) acoerce, &(astate->elemfunc));
	}

	/*
	 * Use array_map to apply the function to each array element.
	 *
	 * We pass on the desttypmod and isExplicit flags whether or not the
	 * function wants them.
	 *
	 * Note: coercion functions are assumed to not use collation.
	 */
	InitFunctionCallInfoData(locfcinfo, &(astate->elemfunc), 3,
							 InvalidOid, NULL, NULL);
	locfcinfo.arg[0] = PointerGetDatum(array);
	locfcinfo.arg[1] = Int32GetDatum(acoerce->resulttypmod);
	locfcinfo.arg[2] = BoolGetDatum(acoerce->isExplicit);
	locfcinfo.argnull[0] = false;
	locfcinfo.argnull[1] = false;
	locfcinfo.argnull[2] = false;

	return array_map(&locfcinfo, ARR_ELEMTYPE(array), astate->resultelemtype,
					 astate->amstate);
}

/* ----------------------------------------------------------------
 *		ExecEvalCurrentOfExpr
 *
 * The planner must convert CURRENT OF into a TidScan qualification.
 * So, we have to be able to do ExecInitExpr on a CurrentOfExpr,
 * but we shouldn't ever actually execute it.
 * ----------------------------------------------------------------
 */
static Datum
ExecEvalCurrentOfExpr(ExprState *exprstate, ExprContext *econtext,
					  bool *isNull, ExprDoneCond *isDone)
{
	elog(ERROR, "CURRENT OF cannot be executed");
	return 0;					/* keep compiler quiet */
}


/*
 * ExecEvalExprSwitchContext
 *
 * Same as ExecEvalExpr, but get into the right allocation context explicitly.
 */
Datum
ExecEvalExprSwitchContext(ExprState *expression,
						  ExprContext *econtext,
						  bool *isNull,
						  ExprDoneCond *isDone)
{
	Datum		retDatum;
	MemoryContext oldContext;

	oldContext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);
	retDatum = ExecEvalExpr(expression, econtext, isNull, isDone);
	MemoryContextSwitchTo(oldContext);
	return retDatum;
}


/*
 * ExecInitExpr: prepare an expression tree for execution
 *
 * This function builds and returns an ExprState tree paralleling the given
 * Expr node tree.	The ExprState tree can then be handed to ExecEvalExpr
 * for execution.  Because the Expr tree itself is read-only as far as
 * ExecInitExpr and ExecEvalExpr are concerned, several different executions
 * of the same plan tree can occur concurrently.
 *
 * This must be called in a memory context that will last as long as repeated
 * executions of the expression are needed.  Typically the context will be
 * the same as the per-query context of the associated ExprContext.
 *
 * Any Aggref, WindowFunc, or SubPlan nodes found in the tree are added to the
 * lists of such nodes held by the parent PlanState. Otherwise, we do very
 * little initialization here other than building the state-node tree.	Any
 * nontrivial work associated with initializing runtime info for a node should
 * happen during the first actual evaluation of that node.	(This policy lets
 * us avoid work if the node is never actually evaluated.)
 *
 * Note: there is no ExecEndExpr function; we assume that any resource
 * cleanup needed will be handled by just releasing the memory context
 * in which the state tree is built.  Functions that require additional
 * cleanup work can register a shutdown callback in the ExprContext.
 *
 *	'node' is the root of the expression tree to examine
 *	'parent' is the PlanState node that owns the expression.
 *
 * 'parent' may be NULL if we are preparing an expression that is not
 * associated with a plan tree.  (If so, it can't have aggs or subplans.)
 * This case should usually come through ExecPrepareExpr, not directly here.
 */
ExprState *
ExecInitExpr(Expr *node, PlanState *parent)
{
	ExprState  *state;

	if (node == NULL)
		return NULL;

	/* Guard against stack overflow due to overly complex expressions */
	check_stack_depth();

	switch (nodeTag(node))
	{
		case T_Var:
			/* varattno == InvalidAttrNumber means it's a whole-row Var */
			if (((Var *) node)->varattno == InvalidAttrNumber)
			{
				WholeRowVarExprState *wstate = makeNode(WholeRowVarExprState);

				wstate->parent = parent;
				wstate->wrv_junkFilter = NULL;
				state = (ExprState *) wstate;
				state->evalfunc = (ExprStateEvalFunc) ExecEvalWholeRowVar;
			}
			else
			{
				state = (ExprState *) makeNode(ExprState);
				state->evalfunc = ExecEvalScalarVar;
			}
			break;
		case T_Const:
			state = (ExprState *) makeNode(ExprState);
			state->evalfunc = ExecEvalConst;
			break;
		case T_Param:
			state = (ExprState *) makeNode(ExprState);
			switch (((Param *) node)->paramkind)
			{
				case PARAM_EXEC:
					state->evalfunc = ExecEvalParamExec;
					break;
				case PARAM_EXTERN:
					state->evalfunc = ExecEvalParamExtern;
					break;
				default:
					elog(ERROR, "unrecognized paramkind: %d",
						 (int) ((Param *) node)->paramkind);
					break;
			}
			break;
		case T_CoerceToDomainValue:
			state = (ExprState *) makeNode(ExprState);
			state->evalfunc = ExecEvalCoerceToDomainValue;
			break;
		case T_CaseTestExpr:
			state = (ExprState *) makeNode(ExprState);
			state->evalfunc = ExecEvalCaseTestExpr;
			break;
		case T_Aggref:
			{
				Aggref	   *aggref = (Aggref *) node;
				AggrefExprState *astate = makeNode(AggrefExprState);

				astate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalAggref;
				if (parent && IsA(parent, AggState))
				{
					AggState   *aggstate = (AggState *) parent;
					int			naggs;

					aggstate->aggs = lcons(astate, aggstate->aggs);
					naggs = ++aggstate->numaggs;

					astate->args = (List *) ExecInitExpr((Expr *) aggref->args,
														 parent);

					/*
					 * Complain if the aggregate's arguments contain any
					 * aggregates; nested agg functions are semantically
					 * nonsensical.  (This should have been caught earlier,
					 * but we defend against it here anyway.)
					 */
					if (naggs != aggstate->numaggs)
						ereport(ERROR,
								(errcode(ERRCODE_GROUPING_ERROR),
						errmsg("aggregate function calls cannot be nested")));
				}
				else
				{
					/* planner messed up */
					elog(ERROR, "Aggref found in non-Agg plan node");
				}
				state = (ExprState *) astate;
			}
			break;
		case T_WindowFunc:
			{
				WindowFunc *wfunc = (WindowFunc *) node;
				WindowFuncExprState *wfstate = makeNode(WindowFuncExprState);

				wfstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalWindowFunc;
				if (parent && IsA(parent, WindowAggState))
				{
					WindowAggState *winstate = (WindowAggState *) parent;
					int			nfuncs;

					winstate->funcs = lcons(wfstate, winstate->funcs);
					nfuncs = ++winstate->numfuncs;
					if (wfunc->winagg)
						winstate->numaggs++;

					wfstate->args = (List *) ExecInitExpr((Expr *) wfunc->args,
														  parent);

					/*
					 * Complain if the windowfunc's arguments contain any
					 * windowfuncs; nested window functions are semantically
					 * nonsensical.  (This should have been caught earlier,
					 * but we defend against it here anyway.)
					 */
					if (nfuncs != winstate->numfuncs)
						ereport(ERROR,
								(errcode(ERRCODE_WINDOWING_ERROR),
						  errmsg("window function calls cannot be nested")));
				}
				else
				{
					/* planner messed up */
					elog(ERROR, "WindowFunc found in non-WindowAgg plan node");
				}
				state = (ExprState *) wfstate;
			}
			break;
		case T_ArrayRef:
			{
				ArrayRef   *aref = (ArrayRef *) node;
				ArrayRefExprState *astate = makeNode(ArrayRefExprState);

				astate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalArrayRef;
				astate->refupperindexpr = (List *)
					ExecInitExpr((Expr *) aref->refupperindexpr, parent);
				astate->reflowerindexpr = (List *)
					ExecInitExpr((Expr *) aref->reflowerindexpr, parent);
				astate->refexpr = ExecInitExpr(aref->refexpr, parent);
				astate->refassgnexpr = ExecInitExpr(aref->refassgnexpr,
													parent);
				/* do one-time catalog lookups for type info */
				astate->refattrlength = get_typlen(aref->refarraytype);
				get_typlenbyvalalign(aref->refelemtype,
									 &astate->refelemlength,
									 &astate->refelembyval,
									 &astate->refelemalign);
				state = (ExprState *) astate;
			}
			break;
		case T_FuncExpr:
			{
				FuncExpr   *funcexpr = (FuncExpr *) node;
				FuncExprState *fstate = makeNode(FuncExprState);

				/*
				 * Ordinary non-set-returning functions use ExecEvalFunc
				 * initially.  After the first call, they may be switched over
				 * to use an ExecEvalFuncSimple* fast path if eligible.
				 *
				 * Set-returning functions use ExecEvalFuncDematerialize
				 * initially, changing to ExecEvalFuncSRF if the function
				 * chooses value-per-call mode.
				 */
				if (!funcexpr->funcretset)
					fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFunc;
				else
					fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFuncDematerialize;

				fstate->args = (List *)
					ExecInitExpr((Expr *) funcexpr->args, parent);
				fstate->func.fn_oid = InvalidOid;		/* not initialized */
				state = (ExprState *) fstate;
			}
			break;
		case T_OpExpr:
			{
				OpExpr	   *opexpr = (OpExpr *) node;
				FuncExprState *fstate = makeNode(FuncExprState);

				if (!opexpr->opretset)
					fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFunc;
				else
					fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFuncDematerialize;

				fstate->args = (List *)
					ExecInitExpr((Expr *) opexpr->args, parent);
				fstate->func.fn_oid = InvalidOid;		/* not initialized */
				state = (ExprState *) fstate;
			}
			break;
		case T_DistinctExpr:
			{
				DistinctExpr *distinctexpr = (DistinctExpr *) node;
				FuncExprState *fstate = makeNode(FuncExprState);

				fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalDistinct;
				fstate->args = (List *)
					ExecInitExpr((Expr *) distinctexpr->args, parent);
				fstate->func.fn_oid = InvalidOid;		/* not initialized */
				state = (ExprState *) fstate;
			}
			break;
		case T_NullIfExpr:
			{
				NullIfExpr *nullifexpr = (NullIfExpr *) node;
				FuncExprState *fstate = makeNode(FuncExprState);

				fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalNullIf;
				fstate->args = (List *)
					ExecInitExpr((Expr *) nullifexpr->args, parent);
				fstate->func.fn_oid = InvalidOid;		/* not initialized */
				state = (ExprState *) fstate;
			}
			break;
		case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr *opexpr = (ScalarArrayOpExpr *) node;
				ScalarArrayOpExprState *sstate = makeNode(ScalarArrayOpExprState);

				sstate->fxprstate.xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalScalarArrayOp;
				sstate->fxprstate.args = (List *)
					ExecInitExpr((Expr *) opexpr->args, parent);
				sstate->fxprstate.func.fn_oid = InvalidOid;		/* not initialized */
				sstate->element_type = InvalidOid;		/* ditto */
				state = (ExprState *) sstate;
			}
			break;
		case T_BoolExpr:
			{
				BoolExpr   *boolexpr = (BoolExpr *) node;
				BoolExprState *bstate = makeNode(BoolExprState);

				switch (boolexpr->boolop)
				{
					case AND_EXPR:
						bstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalAnd;
						break;
					case OR_EXPR:
						bstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalOr;
						break;
					case NOT_EXPR:
						bstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalNot;
						break;
					default:
						elog(ERROR, "unrecognized boolop: %d",
							 (int) boolexpr->boolop);
						break;
				}
				bstate->args = (List *)
					ExecInitExpr((Expr *) boolexpr->args, parent);
				state = (ExprState *) bstate;
			}
			break;
		case T_SubPlan:
			{
				SubPlan    *subplan = (SubPlan *) node;
				SubPlanState *sstate;

				if (!parent)
					elog(ERROR, "SubPlan found with no parent plan");

				sstate = ExecInitSubPlan(subplan, parent);

				/* Add SubPlanState nodes to parent->subPlan */
				parent->subPlan = lappend(parent->subPlan, sstate);

				state = (ExprState *) sstate;
			}
			break;
		case T_AlternativeSubPlan:
			{
				AlternativeSubPlan *asplan = (AlternativeSubPlan *) node;
				AlternativeSubPlanState *asstate;

				if (!parent)
					elog(ERROR, "AlternativeSubPlan found with no parent plan");

				asstate = ExecInitAlternativeSubPlan(asplan, parent);

				state = (ExprState *) asstate;
			}
			break;
		case T_FieldSelect:
			{
				FieldSelect *fselect = (FieldSelect *) node;
				FieldSelectState *fstate = makeNode(FieldSelectState);

				fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFieldSelect;
				fstate->arg = ExecInitExpr(fselect->arg, parent);
				fstate->argdesc = NULL;
				state = (ExprState *) fstate;
			}
			break;
		case T_FieldStore:
			{
				FieldStore *fstore = (FieldStore *) node;
				FieldStoreState *fstate = makeNode(FieldStoreState);

				fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFieldStore;
				fstate->arg = ExecInitExpr(fstore->arg, parent);
				fstate->newvals = (List *) ExecInitExpr((Expr *) fstore->newvals, parent);
				fstate->argdesc = NULL;
				state = (ExprState *) fstate;
			}
			break;
		case T_RelabelType:
			{
				RelabelType *relabel = (RelabelType *) node;
				GenericExprState *gstate = makeNode(GenericExprState);

				gstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalRelabelType;
				gstate->arg = ExecInitExpr(relabel->arg, parent);
				state = (ExprState *) gstate;
			}
			break;
		case T_CoerceViaIO:
			{
				CoerceViaIO *iocoerce = (CoerceViaIO *) node;
				CoerceViaIOState *iostate = makeNode(CoerceViaIOState);
				Oid			iofunc;
				bool		typisvarlena;

				iostate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalCoerceViaIO;
				iostate->arg = ExecInitExpr(iocoerce->arg, parent);
				/* lookup the result type's input function */
				getTypeInputInfo(iocoerce->resulttype, &iofunc,
								 &iostate->intypioparam);
				fmgr_info(iofunc, &iostate->infunc);
				/* lookup the input type's output function */
				getTypeOutputInfo(exprType((Node *) iocoerce->arg),
								  &iofunc, &typisvarlena);
				fmgr_info(iofunc, &iostate->outfunc);
				state = (ExprState *) iostate;
			}
			break;
		case T_ArrayCoerceExpr:
			{
				ArrayCoerceExpr *acoerce = (ArrayCoerceExpr *) node;
				ArrayCoerceExprState *astate = makeNode(ArrayCoerceExprState);

				astate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalArrayCoerceExpr;
				astate->arg = ExecInitExpr(acoerce->arg, parent);
				astate->resultelemtype = get_element_type(acoerce->resulttype);
				if (astate->resultelemtype == InvalidOid)
					ereport(ERROR,
							(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
							 errmsg("target type is not an array")));
				/* Arrays over domains aren't supported yet */
				Assert(getBaseType(astate->resultelemtype) ==
					   astate->resultelemtype);
				astate->elemfunc.fn_oid = InvalidOid;	/* not initialized */
				astate->amstate = (ArrayMapState *) palloc0(sizeof(ArrayMapState));
				state = (ExprState *) astate;
			}
			break;
		case T_ConvertRowtypeExpr:
			{
				ConvertRowtypeExpr *convert = (ConvertRowtypeExpr *) node;
				ConvertRowtypeExprState *cstate = makeNode(ConvertRowtypeExprState);

				cstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalConvertRowtype;
				cstate->arg = ExecInitExpr(convert->arg, parent);
				state = (ExprState *) cstate;
			}
			break;
		case T_CaseExpr:
			{
				CaseExpr   *caseexpr = (CaseExpr *) node;
				CaseExprState *cstate = makeNode(CaseExprState);
				List	   *outlist = NIL;
				ListCell   *l;

				cstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalCase;
				cstate->arg = ExecInitExpr(caseexpr->arg, parent);
				foreach(l, caseexpr->args)
				{
					CaseWhen   *when = (CaseWhen *) lfirst(l);
					CaseWhenState *wstate = makeNode(CaseWhenState);

					Assert(IsA(when, CaseWhen));
					wstate->xprstate.evalfunc = NULL;	/* not used */
					wstate->xprstate.expr = (Expr *) when;
					wstate->expr = ExecInitExpr(when->expr, parent);
					wstate->result = ExecInitExpr(when->result, parent);
					outlist = lappend(outlist, wstate);
				}
				cstate->args = outlist;
				cstate->defresult = ExecInitExpr(caseexpr->defresult, parent);
				state = (ExprState *) cstate;
			}
			break;
		case T_ArrayExpr:
			{
				ArrayExpr  *arrayexpr = (ArrayExpr *) node;
				ArrayExprState *astate = makeNode(ArrayExprState);
				List	   *outlist = NIL;
				ListCell   *l;

				astate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalArray;
				foreach(l, arrayexpr->elements)
				{
					Expr	   *e = (Expr *) lfirst(l);
					ExprState  *estate;

					estate = ExecInitExpr(e, parent);
					outlist = lappend(outlist, estate);
				}
				astate->elements = outlist;
				/* do one-time catalog lookup for type info */
				get_typlenbyvalalign(arrayexpr->element_typeid,
									 &astate->elemlength,
									 &astate->elembyval,
									 &astate->elemalign);
				state = (ExprState *) astate;
			}
			break;
		case T_RowExpr:
			{
				RowExpr    *rowexpr = (RowExpr *) node;
				RowExprState *rstate = makeNode(RowExprState);
				Form_pg_attribute *attrs;
				List	   *outlist = NIL;
				ListCell   *l;
				int			i;

				rstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalRow;
				/* Build tupdesc to describe result tuples */
				if (rowexpr->row_typeid == RECORDOID)
				{
					/* generic record, use runtime type assignment */
					rstate->tupdesc = ExecTypeFromExprList(rowexpr->args,
														   rowexpr->colnames);
					BlessTupleDesc(rstate->tupdesc);
					/* we won't need to redo this at runtime */
				}
				else
				{
					/* it's been cast to a named type, use that */
					rstate->tupdesc = lookup_rowtype_tupdesc_copy(rowexpr->row_typeid, -1);
				}
				/* Set up evaluation, skipping any deleted columns */
				Assert(list_length(rowexpr->args) <= rstate->tupdesc->natts);
				attrs = rstate->tupdesc->attrs;
				i = 0;
				foreach(l, rowexpr->args)
				{
					Expr	   *e = (Expr *) lfirst(l);
					ExprState  *estate;

					if (!attrs[i]->attisdropped)
					{
						/*
						 * Guard against ALTER COLUMN TYPE on rowtype since
						 * the RowExpr was created.  XXX should we check
						 * typmod too?	Not sure we can be sure it'll be the
						 * same.
						 */
						if (exprType((Node *) e) != attrs[i]->atttypid)
							ereport(ERROR,
									(errcode(ERRCODE_DATATYPE_MISMATCH),
									 errmsg("ROW() column has type %s instead of type %s",
										format_type_be(exprType((Node *) e)),
									   format_type_be(attrs[i]->atttypid))));
					}
					else
					{
						/*
						 * Ignore original expression and insert a NULL. We
						 * don't really care what type of NULL it is, so
						 * always make an int4 NULL.
						 */
						e = (Expr *) makeNullConst(INT4OID, -1, InvalidOid);
					}
					estate = ExecInitExpr(e, parent);
					outlist = lappend(outlist, estate);
					i++;
				}
				rstate->args = outlist;
				state = (ExprState *) rstate;
			}
			break;
		case T_RowCompareExpr:
			{
				RowCompareExpr *rcexpr = (RowCompareExpr *) node;
				RowCompareExprState *rstate = makeNode(RowCompareExprState);
				int			nopers = list_length(rcexpr->opnos);
				List	   *outlist;
				ListCell   *l;
				ListCell   *l2;
				ListCell   *l3;
				int			i;

				rstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalRowCompare;
				Assert(list_length(rcexpr->largs) == nopers);
				outlist = NIL;
				foreach(l, rcexpr->largs)
				{
					Expr	   *e = (Expr *) lfirst(l);
					ExprState  *estate;

					estate = ExecInitExpr(e, parent);
					outlist = lappend(outlist, estate);
				}
				rstate->largs = outlist;
				Assert(list_length(rcexpr->rargs) == nopers);
				outlist = NIL;
				foreach(l, rcexpr->rargs)
				{
					Expr	   *e = (Expr *) lfirst(l);
					ExprState  *estate;

					estate = ExecInitExpr(e, parent);
					outlist = lappend(outlist, estate);
				}
				rstate->rargs = outlist;
				Assert(list_length(rcexpr->opfamilies) == nopers);
				rstate->funcs = (FmgrInfo *) palloc(nopers * sizeof(FmgrInfo));
				rstate->collations = (Oid *) palloc(nopers * sizeof(Oid));
				i = 0;
				forthree(l, rcexpr->opnos, l2, rcexpr->opfamilies, l3, rcexpr->inputcollids)
				{
					Oid			opno = lfirst_oid(l);
					Oid			opfamily = lfirst_oid(l2);
					Oid			inputcollid = lfirst_oid(l3);
					int			strategy;
					Oid			lefttype;
					Oid			righttype;
					Oid			proc;

					get_op_opfamily_properties(opno, opfamily, false,
											   &strategy,
											   &lefttype,
											   &righttype);
					proc = get_opfamily_proc(opfamily,
											 lefttype,
											 righttype,
											 BTORDER_PROC);

					/*
					 * If we enforced permissions checks on index support
					 * functions, we'd need to make a check here.  But the
					 * index support machinery doesn't do that, and neither
					 * does this code.
					 */
					fmgr_info(proc, &(rstate->funcs[i]));
					rstate->collations[i] = inputcollid;
					i++;
				}
				state = (ExprState *) rstate;
			}
			break;
		case T_CoalesceExpr:
			{
				CoalesceExpr *coalesceexpr = (CoalesceExpr *) node;
				CoalesceExprState *cstate = makeNode(CoalesceExprState);
				List	   *outlist = NIL;
				ListCell   *l;

				cstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalCoalesce;
				foreach(l, coalesceexpr->args)
				{
					Expr	   *e = (Expr *) lfirst(l);
					ExprState  *estate;

					estate = ExecInitExpr(e, parent);
					outlist = lappend(outlist, estate);
				}
				cstate->args = outlist;
				state = (ExprState *) cstate;
			}
			break;
		case T_MinMaxExpr:
			{
				MinMaxExpr *minmaxexpr = (MinMaxExpr *) node;
				MinMaxExprState *mstate = makeNode(MinMaxExprState);
				List	   *outlist = NIL;
				ListCell   *l;
				TypeCacheEntry *typentry;

				mstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalMinMax;
				foreach(l, minmaxexpr->args)
				{
					Expr	   *e = (Expr *) lfirst(l);
					ExprState  *estate;

					estate = ExecInitExpr(e, parent);
					outlist = lappend(outlist, estate);
				}
				mstate->args = outlist;
				/* Look up the btree comparison function for the datatype */
				typentry = lookup_type_cache(minmaxexpr->minmaxtype,
											 TYPECACHE_CMP_PROC);
				if (!OidIsValid(typentry->cmp_proc))
					ereport(ERROR,
							(errcode(ERRCODE_UNDEFINED_FUNCTION),
							 errmsg("could not identify a comparison function for type %s",
									format_type_be(minmaxexpr->minmaxtype))));

				/*
				 * If we enforced permissions checks on index support
				 * functions, we'd need to make a check here.  But the index
				 * support machinery doesn't do that, and neither does this
				 * code.
				 */
				fmgr_info(typentry->cmp_proc, &(mstate->cfunc));
				state = (ExprState *) mstate;
			}
			break;
		case T_XmlExpr:
			{
				XmlExpr    *xexpr = (XmlExpr *) node;
				XmlExprState *xstate = makeNode(XmlExprState);
				List	   *outlist;
				ListCell   *arg;

				xstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalXml;
				outlist = NIL;
				foreach(arg, xexpr->named_args)
				{
					Expr	   *e = (Expr *) lfirst(arg);
					ExprState  *estate;

					estate = ExecInitExpr(e, parent);
					outlist = lappend(outlist, estate);
				}
				xstate->named_args = outlist;

				outlist = NIL;
				foreach(arg, xexpr->args)
				{
					Expr	   *e = (Expr *) lfirst(arg);
					ExprState  *estate;

					estate = ExecInitExpr(e, parent);
					outlist = lappend(outlist, estate);
				}
				xstate->args = outlist;

				state = (ExprState *) xstate;
			}
			break;
		case T_NullTest:
			{
				NullTest   *ntest = (NullTest *) node;
				NullTestState *nstate = makeNode(NullTestState);

				nstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalNullTest;
				nstate->arg = ExecInitExpr(ntest->arg, parent);
				nstate->argdesc = NULL;
				state = (ExprState *) nstate;
			}
			break;
		case T_BooleanTest:
			{
				BooleanTest *btest = (BooleanTest *) node;
				GenericExprState *gstate = makeNode(GenericExprState);

				gstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalBooleanTest;
				gstate->arg = ExecInitExpr(btest->arg, parent);
				state = (ExprState *) gstate;
			}
			break;
		case T_CoerceToDomain:
			{
				CoerceToDomain *ctest = (CoerceToDomain *) node;
				CoerceToDomainState *cstate = makeNode(CoerceToDomainState);

				cstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalCoerceToDomain;
				cstate->arg = ExecInitExpr(ctest->arg, parent);
				cstate->constraints = GetDomainConstraints(ctest->resulttype);
				state = (ExprState *) cstate;
			}
			break;
		case T_CurrentOfExpr:
			state = (ExprState *) makeNode(ExprState);
			state->evalfunc = ExecEvalCurrentOfExpr;
			break;
		case T_TargetEntry:
			{
				TargetEntry *tle = (TargetEntry *) node;
				GenericExprState *gstate = makeNode(GenericExprState);

				gstate->xprstate.evalfunc = NULL;		/* not used */
				gstate->arg = ExecInitExpr(tle->expr, parent);
				state = (ExprState *) gstate;
			}
			break;
		case T_List:
			{
				List	   *outlist = NIL;
				ListCell   *l;

				foreach(l, (List *) node)
				{
					outlist = lappend(outlist,
									  ExecInitExpr((Expr *) lfirst(l),
												   parent));
				}
				/* Don't fall through to the "common" code below */
				return (ExprState *) outlist;
			}
		default:
			elog(ERROR, "unrecognized node type: %d",
				 (int) nodeTag(node));
			state = NULL;		/* keep compiler quiet */
			break;
	}

	/* Common code for all state-node types */
	state->expr = node;

	return state;
}

/*
 * ExecPrepareExpr --- initialize for expression execution outside a normal
 * Plan tree context.
 *
 * This differs from ExecInitExpr in that we don't assume the caller is
 * already running in the EState's per-query context.  Also, we run the
 * passed expression tree through expression_planner() to prepare it for
 * execution.  (In ordinary Plan trees the regular planning process will have
 * made the appropriate transformations on expressions, but for standalone
 * expressions this won't have happened.)
 */
ExprState *
ExecPrepareExpr(Expr *node, EState *estate)
{
	ExprState  *result;
	MemoryContext oldcontext;

	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	node = expression_planner(node);

	result = ExecInitExpr(node, NULL);

	MemoryContextSwitchTo(oldcontext);

	return result;
}


/* ----------------------------------------------------------------
 *					 ExecQual / ExecTargetList / ExecProject
 * ----------------------------------------------------------------
 */

/* ----------------------------------------------------------------
 *		ExecQual
 *
 *		Evaluates a conjunctive boolean expression (qual list) and
 *		returns true iff none of the subexpressions are false.
 *		(We also return true if the list is empty.)
 *
 *	If some of the subexpressions yield NULL but none yield FALSE,
 *	then the result of the conjunction is NULL (ie, unknown)
 *	according to three-valued boolean logic.  In this case,
 *	we return the value specified by the "resultForNull" parameter.
 *
 *	Callers evaluating WHERE clauses should pass resultForNull=FALSE,
 *	since SQL specifies that tuples with null WHERE results do not
 *	get selected.  On the other hand, callers evaluating constraint
 *	conditions should pass resultForNull=TRUE, since SQL also specifies
 *	that NULL constraint conditions are not failures.
 *
 *	NOTE: it would not be correct to use this routine to evaluate an
 *	AND subclause of a boolean expression; for that purpose, a NULL
 *	result must be returned as NULL so that it can be properly treated
 *	in the next higher operator (cf. ExecEvalAnd and ExecEvalOr).
 *	This routine is only used in contexts where a complete expression
 *	is being evaluated and we know that NULL can be treated the same
 *	as one boolean result or the other.
 *
 * ----------------------------------------------------------------
 */
bool
ExecQual(List *qual, ExprContext *econtext, bool resultForNull)
{
	bool		result;
	MemoryContext oldContext;
	ListCell   *l;

	/*
	 * debugging stuff
	 */
	EV_printf("ExecQual: qual is ");
	EV_nodeDisplay(qual);
	EV_printf("\n");

	/*
	 * Run in short-lived per-tuple context while computing expressions.
	 */
	oldContext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

	/*
	 * Evaluate the qual conditions one at a time.	If we find a FALSE result,
	 * we can stop evaluating and return FALSE --- the AND result must be
	 * FALSE.  Also, if we find a NULL result when resultForNull is FALSE, we
	 * can stop and return FALSE --- the AND result must be FALSE or NULL in
	 * that case, and the caller doesn't care which.
	 *
	 * If we get to the end of the list, we can return TRUE.  This will happen
	 * when the AND result is indeed TRUE, or when the AND result is NULL (one
	 * or more NULL subresult, with all the rest TRUE) and the caller has
	 * specified resultForNull = TRUE.
	 */
	result = true;

	foreach(l, qual)
	{
		ExprState  *clause = (ExprState *) lfirst(l);
		Datum		expr_value;
		bool		isNull;

		expr_value = ExecEvalExpr(clause, econtext, &isNull, NULL);

		if (isNull)
		{
			if (resultForNull == false)
			{
				result = false; /* treat NULL as FALSE */
				break;
			}
		}
		else
		{
			if (!DatumGetBool(expr_value))
			{
				result = false; /* definitely FALSE */
				break;
			}
		}
	}

	MemoryContextSwitchTo(oldContext);

	return result;
}

/*
 * Number of items in a tlist (including any resjunk items!)
 */
int
ExecTargetListLength(List *targetlist)
{
	/* This used to be more complex, but fjoins are dead */
	return list_length(targetlist);
}

/*
 * Number of items in a tlist, not including any resjunk items
 */
int
ExecCleanTargetListLength(List *targetlist)
{
	int			len = 0;
	ListCell   *tl;

	foreach(tl, targetlist)
	{
		TargetEntry *curTle = (TargetEntry *) lfirst(tl);

		Assert(IsA(curTle, TargetEntry));
		if (!curTle->resjunk)
			len++;
	}
	return len;
}

/*
 * ExecTargetList
 *		Evaluates a targetlist with respect to the given
 *		expression context.  Returns TRUE if we were able to create
 *		a result, FALSE if we have exhausted a set-valued expression.
 *
 * Results are stored into the passed values and isnull arrays.
 * The caller must provide an itemIsDone array that persists across calls.
 *
 * The expressions are evaluated in the current memory context.
 *
 * As with ExecEvalExpr, the caller should pass isDone = NULL if not
 * prepared to deal with sets of result tuples.  Otherwise, a return
 * of *isDone = ExprMultipleResult signifies a set element, and a return
 * of *isDone = ExprEndResult signifies end of the set of tuples.
 * We assume that *isDone has been initialized to ExprSingleResult by caller.
 */
static bool
ExecTargetList(List *targetlist,
			   ExprContext *econtext,
			   Datum *values,
			   bool *isnull,
			   ExprDoneCond *itemIsDone,
			   ExprDoneCond *isDone)
{
	ListCell   *tl;
	bool		haveDoneSets;

	/*
	 * evaluate all the expressions in the target list
	 */
	haveDoneSets = false;		/* any exhausted set exprs in tlist? */

	foreach(tl, targetlist)
	{
		GenericExprState *gstate = (GenericExprState *) lfirst(tl);
		TargetEntry *tle = (TargetEntry *) gstate->xprstate.expr;
		AttrNumber	resind = tle->resno - 1;

		values[resind] = ExecEvalExpr(gstate->arg,
									  econtext,
									  &isnull[resind],
									  isDone ? &itemIsDone[resind] : NULL);

		if (isDone && itemIsDone[resind] != ExprSingleResult)
		{
			if (itemIsDone[resind] == ExprMultipleResult)
			{
				/* we have undone sets in the tlist, set flag */
				*isDone = ExprMultipleResult;
			}
			else
			{
				/* we have done sets in the tlist, set flag for that */
				haveDoneSets = true;
			}
		}
	}

	if (haveDoneSets)
	{
		/*
		 * note: can't get here unless we verified isDone != NULL
		 */
		if (*isDone == ExprSingleResult)
		{
			/*
			 * all sets are done, so report that tlist expansion is complete.
			 */
			*isDone = ExprEndResult;
			return false;
		}
		else
		{
			/*
			 * We have some done and some undone sets.	Restart the done ones
			 * so that we can deliver a tuple (if possible).
			 */
			foreach(tl, targetlist)
			{
				GenericExprState *gstate = (GenericExprState *) lfirst(tl);
				TargetEntry *tle = (TargetEntry *) gstate->xprstate.expr;
				AttrNumber	resind = tle->resno - 1;

				if (itemIsDone[resind] == ExprEndResult)
				{
					values[resind] = ExecEvalExpr(gstate->arg,
												  econtext,
												  &isnull[resind],
												  &itemIsDone[resind]);

					if (itemIsDone[resind] == ExprEndResult)
					{
						/*
						 * Oh dear, this item is returning an empty set. Guess
						 * we can't make a tuple after all.
						 */
						*isDone = ExprEndResult;
						break;
					}
				}
			}

			/*
			 * If we cannot make a tuple because some sets are empty, invoke
			 * the ExprContext's registered callbacks to reset the remaining
			 * unfinished SRFs so they'll start fresh for the next cycle.
			 *
			 * If other expressions outside the targetlist have registered
			 * callbacks in the same ExprContext, note that they'll be called
			 * too.  Wherever this seems likely to be a problem, a workaround
			 * is to use a separate ExprContext for those other expressions.
			 */
			if (*isDone == ExprEndResult)
			{
				ShutdownExprContext(econtext, true);
				return false;
			}
		}
	}

	/* Report success */
	return true;
}

/*
 * ExecProject
 *
 *		projects a tuple based on projection info and stores
 *		it in the previously specified tuple table slot.
 *
 *		Note: the result is always a virtual tuple; therefore it
 *		may reference the contents of the exprContext's scan tuples
 *		and/or temporary results constructed in the exprContext.
 *		If the caller wishes the result to be valid longer than that
 *		data will be valid, he must call ExecMaterializeSlot on the
 *		result slot.
 */
TupleTableSlot *
ExecProject(ProjectionInfo *projInfo, ExprDoneCond *isDone)
{
	TupleTableSlot *slot;
	ExprContext *econtext;
	int			numSimpleVars;

	/*
	 * sanity checks
	 */
	Assert(projInfo != NULL);

	/*
	 * get the projection info we want
	 */
	slot = projInfo->pi_slot;
	econtext = projInfo->pi_exprContext;

	/* Assume single result row until proven otherwise */
	if (isDone)
		*isDone = ExprSingleResult;

	/*
	 * Clear any former contents of the result slot.  This makes it safe for
	 * us to use the slot's Datum/isnull arrays as workspace. (Also, we can
	 * return the slot as-is if we decide no rows can be projected.)
	 */
	ExecClearTuple(slot);

	/*
	 * Force extraction of all input values that we'll need.  The
	 * Var-extraction loops below depend on this, and we are also prefetching
	 * all attributes that will be referenced in the generic expressions.
	 */
	if (projInfo->pi_lastInnerVar > 0)
		slot_getsomeattrs(econtext->ecxt_innertuple,
						  projInfo->pi_lastInnerVar);
	if (projInfo->pi_lastOuterVar > 0)
		slot_getsomeattrs(econtext->ecxt_outertuple,
						  projInfo->pi_lastOuterVar);
	if (projInfo->pi_lastScanVar > 0)
		slot_getsomeattrs(econtext->ecxt_scantuple,
						  projInfo->pi_lastScanVar);

	/*
	 * Assign simple Vars to result by direct extraction of fields from source
	 * slots ... a mite ugly, but fast ...
	 */
	numSimpleVars = projInfo->pi_numSimpleVars;
	if (numSimpleVars > 0)
	{
		Datum	   *values = slot->tts_values;
		bool	   *isnull = slot->tts_isnull;
		int		   *varSlotOffsets = projInfo->pi_varSlotOffsets;
		int		   *varNumbers = projInfo->pi_varNumbers;
		int			i;

		if (projInfo->pi_directMap)
		{
			/* especially simple case where vars go to output in order */
			for (i = 0; i < numSimpleVars; i++)
			{
				char	   *slotptr = ((char *) econtext) + varSlotOffsets[i];
				TupleTableSlot *varSlot = *((TupleTableSlot **) slotptr);
				int			varNumber = varNumbers[i] - 1;

				values[i] = varSlot->tts_values[varNumber];
				isnull[i] = varSlot->tts_isnull[varNumber];
			}
		}
		else
		{
			/* we have to pay attention to varOutputCols[] */
			int		   *varOutputCols = projInfo->pi_varOutputCols;

			for (i = 0; i < numSimpleVars; i++)
			{
				char	   *slotptr = ((char *) econtext) + varSlotOffsets[i];
				TupleTableSlot *varSlot = *((TupleTableSlot **) slotptr);
				int			varNumber = varNumbers[i] - 1;
				int			varOutputCol = varOutputCols[i] - 1;

				values[varOutputCol] = varSlot->tts_values[varNumber];
				isnull[varOutputCol] = varSlot->tts_isnull[varNumber];
			}
		}
	}

	/*
	 * If there are any generic expressions, evaluate them.  It's possible
	 * that there are set-returning functions in such expressions; if so and
	 * we have reached the end of the set, we return the result slot, which we
	 * already marked empty.
	 *
	 * We evaluate the expressions in a dedicated short-term memory context so
	 * that on every call we can free any pass-by-reference results and
	 * garbage left over from the previous call.  We can safely reset this
	 * memory context without disturbing any inputs (such as final aggregate
	 * values) which might come from the regular per-tuple memory context.
	 */
	if (projInfo->pi_targetlist)
	{
		MemoryContext oldcxt;
		bool		ok;

		/* Switch to dedicated per-tuple context while computing expressions. */
		if (!econtext->projection_tuple_memory)
			econtext->projection_tuple_memory =
				AllocSetContextCreate(econtext->ecxt_per_query_memory,
									  "projection_tuple",
									  ALLOCSET_SMALL_INITSIZE,	/* keep a block */
									  ALLOCSET_SMALL_INITSIZE,
									  ALLOCSET_SMALL_MAXSIZE);
		oldcxt = MemoryContextSwitchTo(econtext->projection_tuple_memory);

		/* Free output values and garbage left over from previous evaluation. */
		MemoryContextReset(econtext->projection_tuple_memory);

		ok = ExecTargetList(projInfo->pi_targetlist,
							econtext,
							slot->tts_values,
							slot->tts_isnull,
							projInfo->pi_itemIsDone,
							isDone);

		/* Restore caller's memory context. */
		MemoryContextSwitchTo(oldcxt);

		/* Return empty slot if no more result rows. */
		if (!ok)
		{
			MemoryContextReset(econtext->projection_tuple_memory);
			return slot;
		}
	}

	/*
	 * Successfully formed a result row.  Mark the result slot as containing a
	 * valid virtual tuple.
	 */
	return ExecStoreVirtualTuple(slot);
}
