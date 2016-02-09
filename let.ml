
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let let_decl = DeclTrm("let", [1], [(1,[])], [Simple("term") ; Abstraction("term", "term")])

let lett = 
Rule("let",
 				[Formula("typeOf", [Var("E")], [Var("T1")]) ; Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],

				Formula("typeOf", [Constructor( "let", [Var("E") ; Var("R")])], [Var("T2")]  )  ) 


let letSemantics = 
		[
		Rule("letStep",
			[Formula("value", [Var("V")], [])],
			Formula("step",
				[Constructor( "let", [Var("V") ; Var("R")])],
				[Application(Var("R"), Var("V"))]  )  )
		]

let let_ts = [SpecTerm(let_decl, lett, letSemantics)]

let lett_only = SafeTypedLanguage([], let_ts, None)
let stlc_cbn_let = sl_compose stlc_cbn lett_only
let stlc_cbv_let = sl_compose stlc_cbv lett_only
let stlc_par_let = sl_compose stlc_par lett_only

