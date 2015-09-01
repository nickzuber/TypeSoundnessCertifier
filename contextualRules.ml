
open Batteries
open Aux
open Type_system
open Terms

let rec changeTermArgumentAt arg term = match term with 
  | Var(name) -> if arg = Var(name) then Var(toStringWith' arg) else term
  | Constructor(name, arguments) -> Constructor(name, List.map (changeTermArgumentAt arg) arguments)


(* Here below, it is important that we have step E3 E3', value E1, value E2. I.e. that value premises are AFTER the step, 
   This is because Abella gives always the name Step to that step and you can refer to it easily in the proof. 
   Otherwise, it would be a Step3 and you have to search for the numberwould have to search it 
*)
let contextualRulesBySequential c formalTerms conclusionTerm i var = let rulename = "ctx_" ^ c ^ "_" ^ (string_of_int (i+1)) in 
         let varToStep = List.nth formalTerms i in 
         let conclusionStepped = Formula("step", [conclusionTerm], [changeTermArgumentAt varToStep conclusionTerm]) in 
		 let mustbeValues = List.take i formalTerms in 
		 let valuepremises = fun var -> Formula("value", [var], []) in 
  		  Rule(rulename, Formula("step", [varToStep], [Var(toStringWith' varToStep)])::(List.map valuepremises mustbeValues), conclusionStepped)

let contextualRules c formalTerms conclusionTerm n = let rulename = "ctx_" ^ c ^ "_" ^ (string_of_int n) in 
         let varToStep = List.nth formalTerms (n - 1) in 
         let conclusionStepped = Formula("step", [conclusionTerm], [changeTermArgumentAt varToStep conclusionTerm]) in 
		  Rule(rulename, [Formula("step", [varToStep], [Var(toStringWith' varToStep)])], conclusionStepped)

let generateEachContextualRules signatureTerms termEntry = 
	 match termEntry with DeclTrm(c, kind, ctx, arguments) -> 
		 let (formalTerms, formalAbstractions, theRest) = (getTermsAndTheRestByConstructor c signatureTerms) in
		 let conclusionTerm = (Constructor(c, formalTerms @ formalAbstractions @ theRest)) in 
               match ctx with      
			     | Sequential -> List.mapi (contextualRulesBySequential c formalTerms conclusionTerm) formalTerms 
				 | Contextual infos -> List.map (contextualRules c formalTerms conclusionTerm) infos


let generateContextualRules ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
                List.concat (List.map (generateEachContextualRules signatureTerms) signatureTerms)

let addContextualRules ts = extend ts (generateContextualRules ts)
