
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open GenerateLambdaProlog

let rule_wellModed pred termDecl rule strongBool = 
	let premises = rule_getPremises rule in 
	let vars = if strongBool then term_getExpressionVariables termDecl (rule_getInputTerm rule) (* This part should be better *)
	           else term_getVariables (rule_getInputTerm rule) in 
	let checkAnAlreadyInstantiatedVar pred premise = formula_isPredicate pred premise && List.mem (formula_getFirstInputUpToApp premise) vars in 
	List.for_all (checkAnAlreadyInstantiatedVar pred) premises && 
	if strongBool then List.length premises = List.length vars else true (* it checks all and only the vars from the conclusion  *)
	
let rule_wellModed_strong pred termDecl rule = rule_wellModed pred termDecl rule true
let rule_wellModed_weak pred termDecl rule = rule_wellModed pred termDecl rule false

let type_check_typingRuleForConstructor termDecl typename rule = 
	term_isCanonicalFor (term_getOperator termDecl) (rule_getInputTerm rule) && 
	if rule_wellModed_strong typing termDecl rule then true else raise(Failure (generateRule rule)) &&  
	term_isCanonicalRelaxedFor typename (rule_getOutputTerm rule) 
	
let type_check_typingRuleForEliminator termDecl typename rule = 
	let premises = rule_getPremises rule in 
	let vars = term_getExpressionVariables termDecl (rule_getInputTerm rule) in 
	term_isCanonicalFor (term_getOperator termDecl) (rule_getInputTerm rule) && 
	rule_wellModed_strong typing termDecl rule &&	
	not(vars = []) &&  (* at least the eliminating argument should be there *)	
	List.exists (fun premise -> (formula_getFirstInput premise) = List.hd vars && term_isCanonicalFor typename (formula_getFirstOutput premise)) premises  (* at least the eliminating argument is tested *)	

let type_check_typingRuleForOther termDecl rule = 
	let vars = term_getExpressionVariables termDecl (rule_getInputTerm rule) in 
	term_isCanonicalFor (term_getOperator termDecl) (rule_getInputTerm rule) && 
	rule_wellModed_strong typing termDecl rule &&	
	not(vars = [])  (* at least the eliminating argument should be there *)	

let type_check_typingRuleError termDecl rule = 
	term_isCanonicalFor (term_getOperator termDecl) (rule_getInputTerm rule) && 
	rule_wellModed_strong typing termDecl rule &&
	term_isFreeVar rule (rule_getOutputTerm rule) 

let type_check_reductionRule termDecl rule = 
	rule_isPredicateAndName reduction (term_getOperator termDecl) rule && 
	rule_wellModed_weak valuePred termDecl rule 

let type_check_constructors typename termSpec = 
	type_check_typingRuleForConstructor (specTerm_getSig termSpec) typename (specTerm_getTyping termSpec) &&
	specTerm_getReduction termSpec = []

let type_check_eliminators typename listOfConstructors termSpec = 
	type_check_typingRuleForEliminator (specTerm_getSig termSpec) typename (specTerm_getTyping termSpec)  &&
	List.for_all (type_check_reductionRule (specTerm_getSig termSpec)) (specTerm_getReduction termSpec) &&
	if List.for_all (rule_checkEliminates listOfConstructors) (specTerm_getReduction termSpec) then true else raise(Failure ((String.concat "-" listOfConstructors) ^ (String.concat "\n" (List.map generateRule (specTerm_getReduction termSpec)))))

let typecheck_typeSpec typeSpec = 
	let typename = type_getOperator (specType_getSig typeSpec) in 
	List.for_all (type_check_constructors typename) (specType_getConstructors typeSpec) &&
	List.for_all (type_check_eliminators typename (specType_getConstructorsNAMES typeSpec)) (specType_getEliminators typeSpec) 

let typecheck_otherSpec termSpec = 
	type_check_typingRuleForOther (specTerm_getSig termSpec) (specTerm_getTyping termSpec) &&
	List.for_all (type_check_reductionRule (specTerm_getSig termSpec)) (specTerm_getReduction termSpec) 

let type_check_errorHandler errordDecl termSpec = 
	type_check_typingRuleForOther (specTerm_getSig termSpec) (specTerm_getTyping termSpec) &&
	List.for_all (type_check_reductionRule (specTerm_getSig termSpec)) (specTerm_getReduction termSpec) &&
	List.exists (rule_checkEliminates [term_getOperator errordDecl]) (specTerm_getReduction termSpec) 

let typecheck_errors errorSpec = if is_none errorSpec then true else 
	let errorTermSpec = (specError_getError errorSpec) in 
	let errordDecl = specTerm_getSig errorTermSpec in 
	type_check_typingRuleError errordDecl (specTerm_getTyping errorTermSpec) &&
	specTerm_getReduction errorTermSpec = [] && 
	List.for_all (type_check_errorHandler errordDecl) (specError_getHandlers errorSpec)
	 
let typecheck_sl sl = 
	if List.for_all typecheck_typeSpec (sl_getTypes sl) && List.for_all typecheck_otherSpec (sl_getOthers sl) && typecheck_errors (sl_getError sl)
	then true 
	else raise(Failure ("The Safe Typed language is not ok. " ^ String.concat "-" (List.concat (List.map specType_getConstructorsNAMES (sl_getTypes sl)))) )
	
