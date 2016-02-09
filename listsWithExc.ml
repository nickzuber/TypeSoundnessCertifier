
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Lists
open Exception

let headSemantics = 
		[
		Rule("headStepEmpty",
			[],
			Formula("step",
				[Constructor( "head", [Constructor( "emptyList", [])])],
				[Constructor( "raise", [Var("E")])] ) ) 
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
				[Constructor( "raise", [Var("E")])] ) ) 
				;
		Rule("tailStepCons",
			[],
			Formula("step",
				[Constructor( "tail", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
				[Var("E2")] ) )
		]  

let lists_ts valpos ctx = [SpecType(list_decl, 
				[SpecTerm(emptyList_decl, emptyList, []) ; 
				 SpecTerm(cons_decl valpos ctx, cons, [])], 
				[SpecTerm(head_decl, head, headSemantics) ;
				 SpecTerm(tail_decl, tail, tailSemantics)])]

let lists_sl valpos ctx = SafeTypedLanguage(lists_ts valpos ctx, [], None)

let lists = lists_sl [1 ; 2] [(1,[]) ; (2,[1])]
let lists_lazy = lists_sl [] [] 
let listsWithExc = sl_compose lists exc

