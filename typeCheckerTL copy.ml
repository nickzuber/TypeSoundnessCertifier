
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open TypeCheckerSL

let tl_popErrors tl = 
	let (errors, restofRules) = List.partition (rule_isPredicate errorPred) (tl_getRules tl) in 
	let (errorTypings, restofRules') = if errors = [] then ([], restofRules) else List.partition (rule_isPredicateAndName typing (rule_getConstructorOfInput (List.hd errors))) restofRules in 
	(errors, errorTypings, tl_setRules tl restofRules')

let tl_popTypingConstructors tl = 
	let existsAreductionRuleFor c rule = c = rule_getConstructorOfInput rule in 
	let onlyTypingConstructors rule = rule_isTypingRule rule && not(List.exists (existsAreductionRuleFor (rule_getConstructorOfInput rule)) (List.filter rule_isReductionRule (tl_getRules tl))) in
	let (typingConstructors, restofRules) = List.partition onlyTypingConstructors (tl_getRules tl) in 
	(typingConstructors, tl_setRules tl restofRules)

let tl_popTypingRules tl = let (typingRules, restofRules) = List.partition rule_isTypingRule (tl_getRules tl) in (typingRules, tl_setRules tl restofRules)
let tl_popReductionRulesForTerm tl c = let (reductionRules, restofRules) = List.partition (rule_isPredicateAndName reduction c) (tl_getRules tl) in (reductionRules, tl_setRules tl restofRules)

let tl_popContextualRules tl = let onlyContextual rule = rule_isPredicate reduction rule && (List.exists (formula_isPredicate reduction) (rule_getPremises rule) || List.exists (formula_isPredicate errorPred) (rule_getPremises rule)) in 
	let (contextualRules, restofRules) = List.partition onlyContextual (tl_getRules tl) in (contextualRules, tl_setRules tl restofRules)
let tl_popValueDefinitions tl = let (valueDefinitions, restofRules) = List.partition (rule_isPredicate valuePred) (tl_getRules tl) in (valueDefinitions, tl_setRules tl restofRules)
		
let typecheck_typingForConstructors_ tl rule = 
	let typ = tl_lookupTypeDecl tl (rule_getConstructorOfOutput rule) in 
	let term = tl_lookupTermDecl tl (rule_getConstructorOfInput rule) in 
	 sl_withConstructor typ term rule

let typecheck_typingForConstructors (sl, tl) = let (typingConstructors, tl') = tl_popTypingConstructors tl in
(*(List.fold_left sl_compose sl (List.map (typecheck_typingForConstructors_ tl) typingConstructors), tl')*) 
	(snd (specTypes_flatten ((List.map (typecheck_typingForConstructors_ tl) typingConstructors), [])), tl')
 
let typecheck_theRestByTypingRules_ (sl, tl) rule = 
	let term = (tl_lookupTermDecl tl (rule_getConstructorOfInput rule)) in 
	let (reductionRules, tl') = tl_popReductionRulesForTerm tl (rule_getConstructorOfInput rule) in  
	if rule_typeCheckFirst rule && List.for_all rule_checkEliminatesSome reductionRules then let typ = tl_lookupTypeDecl tl (rule_getFirstTypeCheck rule) in (sl_withEliminator sl typ term rule reductionRules, tl') 
	else if List.for_all rule_checkFreeReduction reductionRules then (sl_withDerived sl term rule reductionRules, tl') 
	else if sl_containErrors sl && List.exists rule_checkFreeReduction reductionRules && List.exists (rule_checkEliminates [(sl_getErrorConstructor sl)]) reductionRules then 
		(sl_addErrorHandler sl term rule reductionRules, tl') 
	else raise(Failure ("Typechecking error in typing rules: " ^ (rule_getRuleName rule) ^ " with reduction rules: " ^ String.concat " - " (List.map rule_getRuleName reductionRules))) 

let typecheck_theRestByTypingRules (sl, tl) = let (typingRules, tl') = tl_popTypingRules tl in 
	List.fold_left typecheck_theRestByTypingRules_ (sl, tl') typingRules

let typecheck_error tl = let (errors, errorTypings, tl') = tl_popErrors tl in match (errors, errorTypings) with 
| ([],[]) -> (emptySL, tl')
| ([errorDef],[errorTypingRule]) -> (sl_withError (tl_lookupTermDecl tl' (rule_getConstructorOfInput errorDef)) errorTypingRule, tl') 
| otherwise -> raise(Failure "The language has more than one error.") 


(* to do: both contexts and values. Now they simply consume the rules. *)
let typecheck_contexts (sl, tl) = let (contenxtualRules, tl') = tl_popContextualRules tl in (sl, tl')
let typecheck_valueDefinitions (sl, tl) = let (valueDefinitions, tl') = tl_popValueDefinitions tl in (sl, tl')

let typecheck_tl tlInput = 
	let (sl, tl) = typecheck_theRestByTypingRules (typecheck_valueDefinitions (typecheck_typingForConstructors (typecheck_contexts (typecheck_error tlInput)))) in 
	 if tl_isEmpty tl then typecheck_sl sl else raise(Failure "Typed language contains unclassified parts.") 
	
