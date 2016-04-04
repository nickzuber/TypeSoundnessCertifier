
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage

let arrow_decl = DeclType("arrow", [Simple("typ") ; Simple("typ")])
let absImpl_decl = DeclTrm("abs", [], [], [Abstraction("term", "term")])

(* let app_decl = DeclTrm("app", [1 ; 2], Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) *)
let app_decl valpos ctx = DeclTrm("app", valpos, ctx, [Simple("term"); Simple("term")])

let absImpl = 
Rule("abs",
 		 		[Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
      		  	Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])]))


let app = Rule("app",
				[Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
				 Formula("typeOf", [Var("E2")] ,  [Var("T1")])],
				 
				 Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  )
			
let beta = 
[Rule("beta",
				[],
		    	Formula("step", 
						[Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
						[Application(Var("R"), Var("EE"))]  )  ) 
]

let betaCBV = 
[Rule("beta",
				[Formula("value", [Var("EE")], [])],
		    	Formula("step", 
						[Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
						[Application(Var("R"), Var("EE"))]  )  ) 
]
		
let absImpl_ts valpos ctx beta = [SpecType(arrow_decl, 
				[SpecTerm(absImpl_decl, absImpl, [])], 
				[SpecTerm(app_decl valpos ctx, app, beta)])]

let absImpl valpos ctx beta = SafeTypedLanguage(absImpl_ts valpos ctx beta, [], None)

let itlc_cbn = absImpl [1] [(1,[])] beta
let itlc_cbv = absImpl [1 ; 2] [(1,[]) ; (2,[1])] betaCBV
let itlc_par = absImpl [1] [(1,[]) ; (2,[])] beta


