
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let try_decl = DeclTrm("try", [1], [(1,[])], [Simple("term"); Simple("term")])
let raise_decl = DeclTrm("raise", [1], [(1,[])], [Simple("term")])
let excType_decl = DeclType("excType", [])
let excValue_decl = DeclTrm("excValue", [], [], [])

let excValue = 
Rule("excValue",
				[],
				Formula("typeOf", [Constructor( "excValue", [])], [Constructor( "excType",[])]  )  ) 

let tryy = 
Rule("try",
 				[Formula("typeOf", [Var("E1")] ,  [Var("T")]) ;
 			   	Formula("typeOf", [Var("E2")], [Constructor( "arrow", [Constructor( "excType", []) ; Var("T")]) ]  )],

				Formula("typeOf", [Constructor( "try", [Var("E1") ; Var("E2")])], [Var("T")]  )  )

let raisee = 
Rule("raise",
 				[Formula("typeOf", [Var("E")] ,  [Constructor( "excType", [])])],

				Formula("typeOf", [Constructor( "raise", [Var("E")])], [Var("T")])) 


let error_ts = [SpecType(excType_decl, 
				[SpecTerm(excValue_decl, excValue, [])], 
			[])]


let exceptionSemantics = 
 		[
		Rule("tryValue",
  	  			[Formula("value", [Var("E1")], [])],
  			  	Formula("step",
  					[Constructor( "try", [Var("E1") ; Var("E2")])],
					[Var("E1")]  )  ) ;			
     	Rule("tryError",
    			[],
    			Formula("step",
    				[Constructor( "try", [Constructor( "raise", [Var("E1")]) ; Var("E2")])],
					[Constructor( "app",[Var("E2") ; Var("E1")])]  )  )			
		]

let exc_ts = SpecError(SpecTerm(raise_decl, raisee, []), [SpecTerm(try_decl, tryy, exceptionSemantics)])

let exc = SafeTypedLanguage(error_ts, [], Some exc_ts)
let stlc_cbn_exc = sl_compose stlc_cbn exc
let stlc_cbv_exc = sl_compose stlc_cbv exc
let stlc_par_exc = sl_compose stlc_par exc


