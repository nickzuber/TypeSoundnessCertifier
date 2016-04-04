
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc
open Fix
open Let

let letrec_decl = DeclTrm("letrec", [], [], [Abstraction("term", "term") ; Abstraction("term", "term") ; Simple("typ")])

let letrecc = 
Rule("letrec",
	 		    [Hypothetical(Var("T1"), Application(Var("R1"), Var("x")), Var("T1"))  ; Hypothetical(Var("T1"), Application(Var("R2"), Var("x")), Var("T2"))],
	 
	 		    Formula("typeOf", [Constructor( "letrec", [Var("R1") ; Var("R2") ; Var("T1")])], [Var("T2")]  )  ) 
	

let letrecSemantics = 
		[
		Rule("letrecStep",
			[],
			Formula("step",
				[Constructor( "letrec", [Var("R1") ; Var("R2") ; Var("T")])],
				[Constructor( "let", [Constructor( "fix", [Constructor( "abs", [Var("R1") ; Var("T")])]) ; Var("R2")])]
			))]
				
let letrec_ts = [SpecTerm(letrec_decl, letrecc, letrecSemantics)]

let letrecWithType = SafeTypedLanguage([], letrec_ts, None)
let stlc_cbn_letrecWithType = sl_compose (sl_compose stlc_cbn_fix lett_only) letrecWithType
let stlc_cbv_letrecWithType = sl_compose (sl_compose stlc_cbv_fix lett_only) letrecWithType
let stlc_par_letrecWithType = sl_compose (sl_compose stlc_par_fix lett_only) letrecWithType

