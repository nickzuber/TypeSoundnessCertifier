
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let forall_decl = DeclType("all", [Abstraction("typ", "typ")])
let absT_decl = DeclTrm("absT", [], [], [Abstraction("typ", "term")])
let appT_decl = DeclTrm("appT", [1], [(1,[])], [Simple("term"); Simple("typ")])

let absT = 
Rule("absT",
   			[Generic(Application(Var("R2"), Var("x")), Application(Var("R"), Var("x")))],
   		 	Formula("typeOf",     [Constructor( "absT", [Var("R2")])],      [Constructor( "all", [(Var "R")])])) 

let appT = 
Rule("appT",
 			[Formula("typeOf",[Var("E")],[Constructor("all", [Var("R")])]) ],

			Formula("typeOf",  [Constructor( "appT", [Var("E") ; Var("X")])],    [Application(Var("R"),Var("X"))]  )  ) 


let appTSemantics = 
		[
		Rule("betaT",
 	   		[],
 		   	Formula("step",
				[Constructor( "appT", [Constructor( "absT", [Var("R2")]) ; Var("X")])],
    			[Application(Var("R2"), Var("X"))]  )  ) 
		]
		
let forall_ts = [SpecType(forall_decl, 
				[SpecTerm(absT_decl, absT, [])], 
				[SpecTerm(appT_decl, appT, appTSemantics)])]

let forall = SafeTypedLanguage(forall_ts, [], None)

let stlc_cbn_forall = sl_compose stlc_cbn forall
let stlc_cbv_forall = sl_compose stlc_cbv forall
let stlc_par_forall = sl_compose stlc_par forall

