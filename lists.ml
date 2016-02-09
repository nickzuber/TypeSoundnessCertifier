
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let list_decl = DeclType("list", [Simple("typ")])
let emptyList_decl = DeclTrm("emptyList", [], [], [])
let cons_decl valpos ctx = DeclTrm("cons", valpos, ctx, [Simple("term"); Simple("term")])
let head_decl = DeclTrm("head", [1], [(1,[])], [Simple("term")])
let tail_decl = DeclTrm("tail", [1], [(1,[])], [Simple("term")])
let myError_decl = DeclTrm("myError", [], [], [])

let emptyList =
Rule("emptyList",
				[],
	
				Formula("typeOf", [Constructor( "emptyList", [])], [Constructor( "list", [Var("T")])])) 

let cons = 
Rule("cons",
				[Formula("typeOf", [Var("E1")] ,  [Var("T")]) ; Formula("typeOf", [Var("E2")] , [Constructor( "list", [Var("T")])]) ],
				
				Formula("typeOf", [Constructor( "cons", [Var("E1") ; Var("E2")])], [Constructor( "list", [Var("T")])])) 
				
let head = 
Rule("head",
	 			[Formula("typeOf", [Var("E")], [Constructor( "list", [Var("T")])])],
 
 			   	Formula("typeOf", [Constructor( "head", [Var("E")])], [Var("T")]))

let tail = 
Rule("tail",
	 			[Formula("typeOf", [Var("E")], [Constructor( "list", [Var("T")])])],

				Formula("typeOf", [Constructor( "tail", [Var("E")])], [Constructor( "list", [Var("T")])])) 

let error = 
Rule("error",
				[],

				Formula("typeOf", [Constructor( "myError", [])], [Var("T")])) 
			

let headSemantics = 
		[
		Rule("headStepEmpty",
			[],
			Formula("step",
				[Constructor( "head", [Constructor( "emptyList", [])])],
				[Constructor( "myError", [])] ) ) 
				;
		Rule("headStepCons",
			[],
			Formula("step",
				[Constructor( "head", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
				[Var("E1")] ) )
		]   	
let tailSemantics = 
		[
		Rule("tailStepEmpty",
			[],
			Formula("step",
				[Constructor( "tail", [Constructor( "emptyList", [])])],
				[Constructor( "myError", [])] ) ) 
				;
		Rule("tailStepCons",
			[],
			Formula("step",
				[Constructor( "tail", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
				[Var("E2")] ) )
		]  

let lists_ts valpos ctx = [SpecType(list_decl, 
				[SpecTerm(emptyList_decl, emptyList,[]) ; 
				 SpecTerm(cons_decl valpos ctx, cons,[])], 
				[SpecTerm(head_decl, head, headSemantics) ;
				 SpecTerm(tail_decl, tail, tailSemantics)])]

let myError = SpecError(SpecTerm(myError_decl, error, []), [])
let lists_sl valpos ctx = SafeTypedLanguage(lists_ts valpos ctx, [], Some myError)

let lists = lists_sl [1 ; 2] [(1,[]) ; (2,[1])]
let lists_lazy = lists_sl [] [] 

let stlc_cbn_lists = sl_compose stlc_cbn lists
let stlc_cbn_lists_lazy = sl_compose stlc_cbn lists_lazy
let stlc_cbv_lists = sl_compose stlc_cbv lists
let stlc_cbv_lists_lazy = sl_compose stlc_cbv lists_lazy
let stlc_par_lists = sl_compose stlc_par lists
let stlc_par_lists_lazy = sl_compose stlc_par lists_lazy


