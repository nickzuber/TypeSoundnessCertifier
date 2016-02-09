
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc
open Iff
open Lists


let isnil_decl = DeclTrm("isnil", [1], [(1,[])], [Simple("term")])

let isnil = 
Rule("isnil",
	 			[Formula("typeOf", [Var("E")], [Constructor( "list", [Var("T")])])],

				Formula("typeOf", [Constructor( "isnil", [Var("E")])], [Constructor( "bool", [])])) 


let isnilSemantics = 
		[
		Rule("isnilStepEmpty",
			[],
			Formula("step",
				[Constructor( "isnil", [Constructor( "emptyList", [])])],
				[Constructor( "tt", [])] ) ) 
				;
		Rule("isnilStepCons",
			[],
			Formula("step",
				[Constructor( "isnil", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
				[Constructor( "ff", [])] ) )
		]  

let isnil_ts v c = [SpecType(list_decl, 
				[SpecTerm(emptyList_decl, emptyList, []) ; 
				 SpecTerm(cons_decl v c, cons, [])], 
				[SpecTerm(head_decl, head, headSemantics) ;
				 SpecTerm(tail_decl, tail, tailSemantics) ;
				 SpecTerm(isnil_decl, isnil, isnilSemantics)])]


let listsIsNil_ v c = SafeTypedLanguage(isnil_ts v c, [], Some myError)
let listsIsNil = sl_compose (listsIsNil_ [1 ; 2] [(1,[]) ; (2,[1])]) iff
let listsIsNil_lazy = sl_compose (listsIsNil_ [] []) iff

let stlc_cbn_listsIsNil = sl_compose stlc_cbn listsIsNil
let stlc_cbn_listsIsNil_lazy = sl_compose stlc_cbn listsIsNil_lazy
let stlc_cbv_listsIsNil = sl_compose stlc_cbv listsIsNil
let stlc_cbv_listsIsNil_lazy = sl_compose stlc_cbv listsIsNil_lazy
let stlc_par_listsIsNil = sl_compose stlc_par listsIsNil
let stlc_par_listsIsNil_lazy = sl_compose stlc_par listsIsNil_lazy

