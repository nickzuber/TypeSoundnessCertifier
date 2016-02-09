
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc
open Itlc

let fix_decl = DeclTrm("fix", [1], [(1,[])], [Simple("term")])

let fix = 
Rule("fix",
				[Formula("typeOf", [Var("E")], [Constructor( "arrow", [Var("T") ; Var("T")]) ]  )],

				Formula("typeOf", [Constructor( "fix", [Var("E")])], [Var("T")]  )  )


let fixSemantics = 
		[
		Rule("fixStep",
			[Formula("value", [Var("V")], [])],
			Formula("step",
				[Constructor( "fix", [Var("V")])],
					[Constructor( "app", [Var("V") ; Constructor( "fix", [Var("V")])])]  )  )
		]
				
let fix_ts = [SpecTerm(fix_decl, fix, fixSemantics)]

let fix_only = SafeTypedLanguage([], fix_ts, None)
let stlc_cbn_fix = sl_compose stlc_cbn fix_only
let stlc_cbv_fix = sl_compose stlc_cbv fix_only
let stlc_par_fix = sl_compose stlc_par fix_only

let itlc_cbn_fix = sl_compose itlc_cbn fix_only
let itlc_cbv_fix = sl_compose itlc_cbv fix_only
let itlc_par_fix = sl_compose itlc_par fix_only

