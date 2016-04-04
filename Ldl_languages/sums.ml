
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let sum_decl = DeclType("sum", [Simple("typ") ; Simple("typ")])
let inl_decl = DeclTrm("inl", [1], [(1,[])], [Simple("term")])
let inr_decl = DeclTrm("inr", [1], [(1,[])], [Simple("term")])
let case_decl = DeclTrm("case", [1], [(1,[])], [Simple("term"); Abstraction("term", "term") ; Abstraction("term", "term")])

let inl = 
Rule("inl",
				[Formula("typeOf", [Var("E")] ,  [Var("T1")]) ],
				Formula("typeOf", [Constructor( "inl", [Var("E")])], [Constructor( "sum", [Var("T1") ; Var("T2")])]))

let inr = 
Rule("inr",
				[Formula("typeOf", [Var("E")] ,  [Var("T2")]) ],
				Formula("typeOf", [Constructor( "inr", [Var("E") ])], [Constructor( "sum", [Var("T1") ; Var("T2")])]))

let case = 
Rule("case",
 				[Formula("typeOf", [Var("EE")], [Constructor( "sum", [Var("T1") ; Var("T2")]) ]  ) ;
  			  	Hypothetical(Var("T1"), Application(Var("R1"), Var("x")), Var("T")) ;
 			   	Hypothetical(Var("T2"), Application(Var("R2"), Var("x")), Var("T"))],

				Formula("typeOf", [Constructor( "case", [Var("EE") ; Var("R1") ; Var("R2")])], [Var("T")]  )  )


let caseSemantics = 
		[
		Rule("caseStepinl",
			[],
			Formula("step",
				[Constructor( "case", [Constructor( "inl", [Var("EE")]) ; Var("R1") ; Var("R2")])],
				[Application(Var("R1"), Var("EE"))]  )  ) 
				;		
		Rule("caseStepinr",
			[],
			Formula("step",
				[Constructor( "case", [Constructor( "inr", [Var("EE")]) ; Var("R1") ; Var("R2")])],
				[Application(Var("R2"), Var("EE"))]  )  ) 				
		]

let sums_ts = [SpecType(sum_decl, 
				[SpecTerm(inl_decl, inl, []) ; SpecTerm(inr_decl, inr, [])], 
				[SpecTerm(case_decl, case, caseSemantics)])]

let sums = SafeTypedLanguage(sums_ts, [], None)
let stlc_cbn_sums = sl_compose stlc_cbn sums
let stlc_cbv_sums = sl_compose stlc_cbv sums
let stlc_par_sums = sl_compose stlc_par sums

