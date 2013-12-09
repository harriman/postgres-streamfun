/*-------------------------------------------------------------------------
 *
 * funcapi.h
 *	  Definitions for functions which return composite type and/or sets
 *
 * This file must be included by all Postgres modules that either define
 * or call FUNCAPI-callable functions or macros.
 *
 *
 * Copyright (c) 2002-2013, PostgreSQL Global Development Group
 *
 * src/include/funcapi.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef FUNCAPI_H
#define FUNCAPI_H

#include "fmgr.h"
#include "access/tupdesc.h"
#include "executor/executor.h"
#include "executor/tuptable.h"
#include "utils/tuplestore.h"


/*-------------------------------------------------------------------------
 *	Support to ease writing Functions returning composite types
 *-------------------------------------------------------------------------
 *
 * This struct holds arrays of individual attribute information
 * needed to create a tuple from raw C strings. It also requires
 * a copy of the TupleDesc. The information carried here
 * is derived from the TupleDesc, but it is stored here to
 * avoid redundant cpu cycles on each call to an SRF.
 */
typedef struct AttInMetadata
{
	/* full TupleDesc */
	TupleDesc	tupdesc;

	/* array of attribute type input function finfo */
	FmgrInfo   *attinfuncs;

	/* array of attribute type i/o parameter OIDs */
	Oid		   *attioparams;

	/* array of attribute typmod */
	int32	   *atttypmods;
} AttInMetadata;

/*-------------------------------------------------------------------------
 *		Support struct to ease writing Set Returning Functions (SRFs)
 *-------------------------------------------------------------------------
 *
 * This struct holds function context for Set Returning Functions.
 * Use fn_extra to hold a pointer to it across calls
 */
typedef struct FuncCallContext
{
	/*
	 * Number of times we've been called before
	 *
	 * call_cntr is initialized to 0 for you by SRF_FIRSTCALL_INIT(), and
	 * incremented for you every time SRF_RETURN_NEXT() is called.
	 */
	uint32		call_cntr;

	/*
	 * OPTIONAL maximum number of calls
	 *
	 * max_calls is here for convenience only and setting it is optional. If
	 * not set, you must provide alternative means to know when the function
	 * is done.
	 */
	uint32		max_calls;

	/*
	 * OPTIONAL pointer to result slot
	 *
	 * This is obsolete and only present for backwards compatibility, viz,
	 * user-defined SRFs that use the deprecated TupleDescGetSlot().
	 */
	TupleTableSlot *slot;

	/*
	 * OPTIONAL pointer to miscellaneous user-provided context information
	 *
	 * user_fctx is for use as a pointer to your own struct to retain
	 * arbitrary context information between calls of your function.
	 */
	void	   *user_fctx;

	/*
	 * OPTIONAL pointer to struct containing attribute type input metadata
	 *
	 * attinmeta is for use when returning tuples (i.e. composite data types)
	 * and is not used when returning base data types. It is only needed if
	 * you intend to use BuildTupleFromCStrings() to create the return tuple.
	 */
	AttInMetadata *attinmeta;

	/*
	 * memory context used for structures that must live for multiple calls
	 *
	 * multi_call_memory_ctx is set by SRF_FIRSTCALL_INIT() for you, and used
	 * by SRF_RETURN_DONE() for cleanup. It is the most appropriate memory
	 * context for any memory that is to be reused across multiple calls of
	 * the SRF.
	 */
	MemoryContext multi_call_memory_ctx;

	/*
	 * OPTIONAL pointer to struct containing tuple description
	 *
	 * tuple_desc is for use when returning tuples (i.e. composite data types)
	 * and is only needed if you are going to build the tuples with
	 * heap_form_tuple() rather than with BuildTupleFromCStrings(). Note that
	 * the TupleDesc pointer stored here should usually have been run through
	 * BlessTupleDesc() first.
	 */
	TupleDesc	tuple_desc;

} FuncCallContext;

/*----------
 *	Support to ease writing functions returning composite types
 *
 * External declarations:
 * get_call_result_type:
 *		Given a function's call info record, determine the kind of datatype
 *		it is supposed to return.  If resultTypeId isn't NULL, *resultTypeId
 *		receives the actual datatype OID (this is mainly useful for scalar
 *		result types).	If resultTupleDesc isn't NULL, *resultTupleDesc
 *		receives a pointer to a TupleDesc when the result is of a composite
 *		type, or NULL when it's a scalar result or the rowtype could not be
 *		determined.  NB: the tupledesc should be copied if it is to be
 *		accessed over a long period.
 * get_expr_result_type:
 *		Given an expression node, return the same info as for
 *		get_call_result_type.  Note: the cases in which rowtypes cannot be
 *		determined are different from the cases for get_call_result_type.
 * get_func_result_type:
 *		Given only a function's OID, return the same info as for
 *		get_call_result_type.  Note: the cases in which rowtypes cannot be
 *		determined are different from the cases for get_call_result_type.
 *		Do *not* use this if you can use one of the others.
 *----------
 */

/* Type categories for get_call_result_type and siblings */
typedef enum TypeFuncClass
{
	TYPEFUNC_SCALAR,			/* scalar result type */
	TYPEFUNC_COMPOSITE,			/* determinable rowtype result */
	TYPEFUNC_RECORD,			/* indeterminate rowtype result */
	TYPEFUNC_OTHER				/* bogus type, eg pseudotype */
} TypeFuncClass;

extern TypeFuncClass get_call_result_type(FunctionCallInfo fcinfo,
					 Oid *resultTypeId,
					 TupleDesc *resultTupleDesc);
extern TypeFuncClass get_expr_result_type(Node *expr,
					 Oid *resultTypeId,
					 TupleDesc *resultTupleDesc);
extern TypeFuncClass get_func_result_type(Oid functionId,
					 Oid *resultTypeId,
					 TupleDesc *resultTupleDesc);

extern bool resolve_polymorphic_argtypes(int numargs, Oid *argtypes,
							 char *argmodes,
							 Node *call_expr);

extern int get_func_arg_info(HeapTuple procTup,
				  Oid **p_argtypes, char ***p_argnames,
				  char **p_argmodes);

extern int get_func_input_arg_names(Datum proargnames, Datum proargmodes,
						 char ***arg_names);

extern char *get_func_result_name(Oid functionId);

extern TupleDesc build_function_result_tupdesc_d(Datum proallargtypes,
								Datum proargmodes,
								Datum proargnames);
extern TupleDesc build_function_result_tupdesc_t(HeapTuple procTuple);


/*----------
 *	Support to ease writing functions returning composite types
 *
 * External declarations:
 * TupleDesc BlessTupleDesc(TupleDesc tupdesc) - "Bless" a completed tuple
 *		descriptor so that it can be used to return properly labeled tuples.
 *		You need to call this if you are going to use heap_form_tuple directly.
 *		TupleDescGetAttInMetadata does it for you, however, so no need to call
 *		it if you call TupleDescGetAttInMetadata.
 * AttInMetadata *TupleDescGetAttInMetadata(TupleDesc tupdesc) - Build an
 *		AttInMetadata struct based on the given TupleDesc. AttInMetadata can
 *		be used in conjunction with C strings to produce a properly formed
 *		tuple.
 * HeapTuple BuildTupleFromCStrings(AttInMetadata *attinmeta, char **values) -
 *		build a HeapTuple given user data in C string form. values is an array
 *		of C strings, one for each attribute of the return tuple.
 *
 * Macro declarations:
 * HeapTupleGetDatum(HeapTuple tuple) - convert a HeapTuple to a Datum.
 *
 * Obsolete routines and macros:
 * TupleDesc RelationNameGetTupleDesc(const char *relname) - Use to get a
 *		TupleDesc based on a named relation.
 * TupleDesc TypeGetTupleDesc(Oid typeoid, List *colaliases) - Use to get a
 *		TupleDesc based on a type OID.
 * TupleTableSlot *TupleDescGetSlot(TupleDesc tupdesc) - Builds a
 *		TupleTableSlot, which is not needed anymore.
 * TupleGetDatum(TupleTableSlot *slot, HeapTuple tuple) - get a Datum
 *		given a tuple and a slot.
 *----------
 */

#define HeapTupleGetDatum(_tuple)		PointerGetDatum((_tuple)->t_data)
/* obsolete version of above */
#define TupleGetDatum(_slot, _tuple)	PointerGetDatum((_tuple)->t_data)

extern TupleDesc RelationNameGetTupleDesc(const char *relname);
extern TupleDesc TypeGetTupleDesc(Oid typeoid, List *colaliases);

/* from execTuples.c */
extern TupleDesc BlessTupleDesc(TupleDesc tupdesc);
extern AttInMetadata *TupleDescGetAttInMetadata(TupleDesc tupdesc);
extern HeapTuple BuildTupleFromCStrings(AttInMetadata *attinmeta, char **values);
extern TupleTableSlot *TupleDescGetSlot(TupleDesc tupdesc);


/*
 * Convenience macros for returning from set-returning functions.  These are 
 * lower-level than the ones further below that maintain a FuncCallContext.
 *
 * Value-per-call mode:  Use SRF_BASIC_RETURN_END() to return the empty set, 
 * or to finish a result set that has no more items.  To return a value or 
 * NULL, after which the caller will call again to continue the set, use 
 * SRF_BASIC_RETURN_NEXT(datum) or SRF_BASIC_RETURN_NEXT_NULL().  To return 
 * the final value of a set without being called again, you may optionally use 
 * SRF_BASIC_RETURN_NEXT_AND_END(datum) or SRF_BASIC_RETURN_NEXT_NULL_AND_END.
 * 
 * Materialize mode:  The return value and fcinfo->isnull flag are ignored; 
 * so always return 0; and don't use SRF_BASIC_RETURN_NEXT_NULL().  To produce
 * the empty set, or to end an incrementally produced result set, simply 
 * return in any way you choose, with nothing added to the tuplestore; but if 
 * you want the same code path to be shared with value per call mode, use 
 * SRF_BASIC_RETURN_END(), which works in either mode.  To produce a nonempty 
 * set, add some tuples to the tuplestore; then use SRF_BASIC_RETURN_NEXT(0) 
 * if you want to continue adding to the same result set when called again; or 
 * use SRF_BASIC_RETURN_END() or SRF_BASIC_RETURN_NEXT_AND_END(0) to conclude 
 * the result set without being called again.  
 * 
 * Any mode:  When you know the resultinfo->isDone flag already has the right
 * setting (or in materialize mode, will be ignored because you haven't added 
 * to the tuplestore), you can use PG_RETURN_VOID() or simply return 0, saving 
 * one assignment.  The caller initializes isDone = ExprSingleResult before 
 * the first call for each result set, and ExprMultipleResult on the second 
 * and subsequent calls.
 *
 * After a result set has ended, a new result set begins with the next call.
 */
#define SRF_BASIC_RETURN_NEXT(_result) \
	do { \
		((ReturnSetInfo *) fcinfo->resultinfo)->isDone = ExprMultipleResult; \
		PG_RETURN_DATUM(_result); \
	} while (0)

#define SRF_BASIC_RETURN_NEXT_NULL() \
	do { \
		((ReturnSetInfo *) fcinfo->resultinfo)->isDone = ExprMultipleResult; \
		PG_RETURN_NULL(); \
	} while (0)

#define SRF_BASIC_RETURN_NEXT_AND_END(_result) \
	do { \
		((ReturnSetInfo *) fcinfo->resultinfo)->isDone = ExprSingleResult; \
		PG_RETURN_DATUM(_result); \
	} while (0)

#define SRF_BASIC_RETURN_NEXT_NULL_AND_END() \
	do { \
		((ReturnSetInfo *) fcinfo->resultinfo)->isDone = ExprSingleResult; \
		PG_RETURN_NULL(); \
	} while (0)

#define SRF_BASIC_RETURN_END() \
	do { \
		((ReturnSetInfo *) fcinfo->resultinfo)->isDone = ExprEndResult; \
		PG_RETURN_VOID(); \
	} while (0)

/*----------
 *		Support for Set Returning Functions (SRFs)
 *
 * SRFs may optionally use a convenience API which looks something like:
 *
 * Datum
 * my_Set_Returning_Function(PG_FUNCTION_ARGS)
 * {
 *	FuncCallContext    *funcctx;
 *	Datum				result;
 *	MemoryContext		oldcontext;
 *	<user defined declarations>
 *
 *	if (SRF_IS_FIRSTCALL())
 *	{
 *		funcctx = SRF_FIRSTCALL_INIT();
 *		<if result set is to be returned in a tuplestore>
 *			tuplestore = srf_init_materialize_mode(fcinfo);
 *		<endif tuplestore>
 *		// switch context when allocating stuff to be used in later calls
 *		oldcontext = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx);
 *		<user defined code>
 *		<if returning composite>
 *			<build TupleDesc, and perhaps AttInMetaData>
 *		<endif returning composite>
 *		<user defined code>
 *		// return to original context when allocating transient memory
 *		MemoryContextSwitchTo(oldcontext);
 *	}
 *	else
 *	{
 *		funcctx = SRF_PERCALL_SETUP();
 *		<user defined code>
 *	}
 *	<user defined code>
 *
 *	<if using materialize mode>
 *		<put result tuples into tuplestore>
 *		<if you want to be called again to add more tuples to this result set>
 *			SRF_RETURN_NEXT(funcctx, (Datum) 0);
 *		<or if you're finished with this result set>
 *			PG_RETURN_VOID();
 *		<endif>
 *	<endif materialize mode>
 *			
 *	<if using value-per-call mode>
 *		<if all values have been returned already for this result set>
 *			SRF_RETURN_DONE(funcctx);  <or>  SRF_BASIC_RETURN_END();
 *		<or if returning a NULL value>
 *			SRF_RETURN_NEXT_NULL(funcctx);
 *		<or if returning a non-NULL value>
 *			<obtain result Datum>
 *			SRF_RETURN_NEXT(funcctx, result);
 *		<endif>
 *	<endif value-per-call>
 * }
 *----------
 */

/* from funcapi.c */
extern FuncCallContext *init_MultiFuncCall(PG_FUNCTION_ARGS);
extern FuncCallContext *per_MultiFuncCall(PG_FUNCTION_ARGS);
extern void end_MultiFuncCall(PG_FUNCTION_ARGS, FuncCallContext *funcctx);

#define SRF_IS_FIRSTCALL() (fcinfo->flinfo->fn_extra == NULL)

#define SRF_FIRSTCALL_INIT() init_MultiFuncCall(fcinfo)

#define SRF_PERCALL_SETUP() per_MultiFuncCall(fcinfo)

#define SRF_RETURN_NEXT(_funcctx, _result) \
	do { \
		(_funcctx)->call_cntr++; \
		SRF_BASIC_RETURN_NEXT(_result); \
	} while (0)

#define SRF_RETURN_NEXT_NULL(_funcctx) \
	do { \
		(_funcctx)->call_cntr++; \
		SRF_BASIC_RETURN_NEXT_NULL(); \
	} while (0)

#define  SRF_RETURN_DONE(_funcctx) \
	do { \
		end_MultiFuncCall(fcinfo, _funcctx); \
		SRF_BASIC_RETURN_END(); \
	} while (0)


/* from funcapi.c */
extern void srf_check_context(FunctionCallInfo fcinfo);
extern Tuplestorestate *srf_init_materialize_mode(FunctionCallInfo fcinfo);
extern TupleDesc srf_get_expected_tupdesc(FunctionCallInfo fcinfo, bool isrequired);
extern void srf_verify_expected_tupdesc(FunctionCallInfo fcinfo, TupleDesc actualtupdesc);

#endif   /* FUNCAPI_H */
