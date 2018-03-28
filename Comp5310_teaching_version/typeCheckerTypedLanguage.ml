
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open ListManagement
open AlphaConversion
open TypeCheckerProgress
open GenerateLambdaProlog
open LdlToTypedLanguage

(* ck (stands for "check") only serves for not being verbous in the following typechecker. defined in Aux *)

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
let tl_popValueDefinitions tl = let (valueDefinitions, restofRules) = List.partition (rule_isPredicate valuePred) (tl_getRules tl) in (valueDefinitions, tl_setRules tl restofRules)
		

let typecheck_typingForConstructors_ tl rule = 
	let typ = tl_lookupTypeDecl tl (rule_getConstructorOfOutput rule) in 
	let term = tl_lookupTermDecl tl (rule_getConstructorOfInput rule) in 
	 SpecType(typ, [SpecTerm(term, rule, [])], [])

let typecheck_typingForConstructors (ldl, tl) = let (typingConstructors, tl') = tl_popTypingConstructors tl in
	let types = snd (specTypes_flatten ((List.map (typecheck_typingForConstructors_ tl) typingConstructors), [])) in 
	(ldl_addTypes ldl types, tl')
 
let typecheck_theRestByTypingRules_ (ldl, tl) rule = 
	let term = (tl_lookupTermDecl tl (rule_getConstructorOfInput rule)) in 
	let (reductionRules, tl') = tl_popReductionRulesForTerm tl (rule_getConstructorOfInput rule) in  
	if rule_typeCheckFirst rule && List.for_all rule_checkEliminatesSome reductionRules 
		then let typ = tl_lookupTypeDecl tl (rule_getFirstTypeCheck rule) in (ldl_withEliminator ldl typ term rule reductionRules, tl')
		else if List.for_all rule_checkFreeReduction reductionRules 
			then (ldl_withDerived ldl term rule reductionRules, tl') 
			else if ldl_containErrors ldl && List.exists rule_checkFreeReduction reductionRules && List.exists (rule_checkEliminates [(ldl_getErrorConstructor ldl)]) reductionRules 
				then (ldl_addErrorHandler ldl term rule reductionRules, tl') 
				else raise(Failure ("Typechecking error in typing rules: " ^ (rule_getRuleName rule) ^ " with reduction rules: " ^ String.concat " - " (List.map rule_getRuleName reductionRules))) 

let typecheck_theRestByTypingRules (ldl, tl) = let (typingRules, tl') = tl_popTypingRules tl in 
	List.fold_left typecheck_theRestByTypingRules_ (ldl, tl') typingRules

let typecheck_error tl = let (errors, errorTypings, tl') = tl_popErrors tl in match (errors, errorTypings) with 
| ([],[]) -> (emptyLDL, tl')
| ([errorDef],[errorTypingRule]) -> (ldl_withError (tl_lookupTermDecl tl' (rule_getConstructorOfInput errorDef)) errorTypingRule, tl') 
| otherwise -> raise(Failure "The language has more than one error.") 


let typecheck_valueDefinitions (ldl, tl) = let (valueDefinitions, tl') = tl_popValueDefinitions tl in 
	if List.for_all rule_wellFormed1 valueDefinitions 
		then (List.fold_left ldl_addValueDefinitions ldl (List.map positionsCheckedForValuehood valueDefinitions), tl') 
		else raise(Failure "Typecheck TL: Value Definition not in form WF1.")

let typecheck_lists (ldl, tl) = 
	let typecheck_lists_ (ldl, tl) termDecl = 
		(let c = term_getOperator termDecl in 
			let (mainTypingRule, otherTypingRules) = (if termDecl_isSelfList termDecl 
														then (rule_typeOfTheSelfList c, [rule_typeOfEmptyList true c ; rule_typeOfConsList termDecl])
														else (rule_typeOfEmptyList false c, [rule_typeOfConsList termDecl]))
			in (ldl_addType ldl (SpecType(DeclType(c ^ "T", termDecl_getArguments termDecl), [SpecTerm(termDecl, mainTypingRule, otherTypingRules)], [])), tl)) 
	 in List.fold_left typecheck_lists_ (ldl, tl) (tl_getLists tl)

let typecheck_tl_ tlInput =  typecheck_theRestByTypingRules (typecheck_valueDefinitions (typecheck_lists (typecheck_typingForConstructors (typecheck_error tlInput))))
let typecheck_tl tlInput subtyping = 
	let (ldl, tl) = typecheck_tl_ tlInput in 
	let tlInput = renameVariablesIfNeeded tlInput ldl subtyping in 
	let (ldl, tl) = typecheck_tl_ tlInput in 
	 if typecheck_ldl ldl
			then ldl 
			else raise(Failure "TypedLanguage does not typecheck into an Logically designed language.") 

