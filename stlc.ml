
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage

let arrow_decl = DeclType("arrow", [Simple("typ") ; Simple("typ")])
let abs_decl = DeclTrm("abs", [], [], [Abstraction("term", "term") ; Simple("typ") ])
(* let app_decl = DeclTrm("app", [1 ; 2], Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) *)
let app_decl valpos ctx = DeclTrm("app", valpos, ctx, [Simple("term"); Simple("term")])

let abs = Rule("abs",
				[Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
				Formula("typeOf",     [Constructor( "abs", [Var("R") ; Var("T1")])],      
				
				[Constructor( "arrow", [(Var "T1") ; (Var "T2")])]))
			
let app = Rule("app",
				[Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
				 Formula("typeOf", [Var("E2")] ,  [Var("T1")])],
				 
				 Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  )
			
let beta = 
[Rule("beta",
				[],
		    	Formula("step", 
						[Constructor( "app", [Constructor( "abs", [Var("R") ; Var("T")]) ; Var("EE")])],
						[Application(Var("R"), Var("EE"))]  )  ) 
]

let betaCBV = 
[Rule("beta",
				[Formula("value", [Var("EE")], [])],
		    	Formula("step", 
						[Constructor( "app", [Constructor( "abs", [Var("R") ; Var("T")]) ; Var("EE")])],
						[Application(Var("R"), Var("EE"))]  )  ) 
]
		
let arrow_ts valpos ctx beta = [SpecType(arrow_decl, 
				[SpecTerm(abs_decl, abs, [])], 
				[SpecTerm(app_decl valpos ctx, app , beta)])]

let stlc valpos ctx beta = SafeTypedLanguage(arrow_ts valpos ctx beta, [], None)

let stlc_cbn = stlc [1] [(1,[])] beta
let stlc_cbv = stlc [1 ; 2] [(1,[]) ; (2,[1])] betaCBV
let stlc_par = stlc [1] [(1,[]) ; (2,[])] beta

