
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let mu_decl = DeclType("mu", [Abstraction("typ", "typ")])
let fold_decl = DeclTrm("fold", [1], [(1,[])], [Simple("term") ; Abstraction("typ", "typ") ;])
let unfold_decl = DeclTrm("unfold", [1], [(1,[])], [Simple("term")])

let fold = 
Rule("fold",
   			[Formula("typeOf",[Var("E")], [Application(Var("R"), Constructor( "mu", [(Var "R")]))])],
   		 	Formula("typeOf",     [Constructor( "fold", [Var("E") ; Var("R")])],      [Constructor( "mu", [(Var "R")])])) 

let unfold = 
Rule("unfold",
 			[Formula("typeOf",[Var("E")],[Constructor( "mu", [(Var "R")]) ])],
			Formula("typeOf",  [Constructor( "unfold", [Var("E")])],    [Application(Var("R"), Constructor( "mu", [(Var "R")]))])  ) 


let unfoldSemantics = 
		[
		Rule("unfoldStep",
 	   		[Formula("value", [Var("V")], [])],
 		   	Formula("step",
				[Constructor( "unfold", [Constructor( "fold", [Var("V") ; Var("R")])])],
				[Var("V")]  )  ) 
		]
		
let recursive_ts = [SpecType(mu_decl, 
				[SpecTerm(fold_decl, fold, [])], 
				[SpecTerm(unfold_decl, unfold, unfoldSemantics)])]

				
let recursive = SafeTypedLanguage(recursive_ts, [], None)
