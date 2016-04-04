
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let bool_decl = DeclType("bool", [])
let true_decl = DeclTrm("tt", [], [], [])
let false_decl = DeclTrm("ff", [], [], [])
let if_decl valpos ctx = DeclTrm("if", valpos, ctx, [Simple("term") ; Simple("term") ; Simple("term")])

let tt = 
Rule("tt",
	   			[],
				Formula("typeOf",     [Constructor( "tt", [])],      [Constructor( "bool", [])]))

let ff = 
Rule("ff",
	   			[],
				Formula("typeOf",     [Constructor( "ff", [])],      [Constructor( "bool", [])]))

let iff_type = 
Rule("if",
	 			[Formula("typeOf",     [Var("E1")], [Constructor( "bool", []  )]) ;
 				Formula("typeOf", [Var("E2")] ,  [Var("T")]) ;
 			   	Formula("typeOf", [Var("E3")] ,  [Var("T")])],

 			   	Formula("typeOf", [Constructor( "if", [Var("E1") ; Var("E2") ; Var("E3") ])],[Var("T")]  )  )
 

let ifSemantics = 
   		[
		Rule("conditional_true",
	    	[],
	    	Formula("step",
		    	[Constructor( "if", [Constructor( "tt", []) ; Var("E1") ; Var("E2")])],
		   		[Var("E1")]  )  ) 
				;
		Rule("conditional_false",
	    	[],
	    	Formula("step",
				[Constructor( "if", [Constructor( "ff", []) ; Var("E1") ; Var("E2")])],
					[Var("E2")]  )  ) 
		] 

let if_ts valpos ctx = [SpecType(bool_decl, 
				[SpecTerm(true_decl, tt, []) ; 
				 SpecTerm(false_decl, ff, [])], 
				[SpecTerm(if_decl valpos ctx, iff_type, ifSemantics)])]

let iff_sl valpos ctx = SafeTypedLanguage(if_ts valpos ctx, [], None)

let iff = iff_sl [1] [(1,[])]
let iff_par = iff_sl [1] [(1,[]) ; (2,[]) ; (3,[])]

let stlc_cbn_iff = sl_compose stlc_cbn iff
let stlc_cbn_iff_par = sl_compose stlc_cbn iff_par
let stlc_cbv_iff = sl_compose stlc_cbv iff
let stlc_cbv_iff_par = sl_compose stlc_cbv iff_par
let stlc_par_iff = sl_compose stlc_par iff
let stlc_par_iff_par = sl_compose stlc_par iff_par
				
				
(* 
| (specType :: rest, []) -> (rest, [specType]) 
	
	specTypes_flatten ([SpecType(bool_decl, [SpecTerm(true_decl, tt, [])], []) ; SpecType(bool_decl, [SpecTerm(false_decl, ff, [])], []) ], []);;
*)				
