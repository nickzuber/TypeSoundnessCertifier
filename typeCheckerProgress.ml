
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open GenerateLambdaProlog

(* ck (stands for "check") only serves for not being verbous in the following typechecker. defined in Aux *)

let rule_wellFormed1 rule = 
	let vars = term_getVariables (rule_getInputTerm rule) in 
	let checkPremises premise = 
		formula_isPredicate valuePred premise && 
		List.mem (formula_getFirstInputUpToApp premise) vars in  (* it checks premises uses the right predicates and only the vars from the conclusion  *)
(*	ck (vars_disjoint (term_getVariables (rule_getInputTerm rule))) ("rule not in WF1: vars_disjoint : " ^ generateTerm (rule_getInputTerm rule)) && *)
	ck (List.for_all checkPremises (rule_getPremises rule)) ("rule not in WF1: only tests for valuehood of variables that come from the input are allowed. : " ^ generateRule rule) && 
	if formula_isPredicate reduction (rule_getConclusion rule) 
		then ck (list_subset (term_getVariables (formula_getFirstOutputUpToApp (rule_getConclusion rule))) vars) ("rule not in WF1: variables in target do not come from source")  
		else true
	
let rule_wellFormed2 termDecl rule = 
	let vars = term_getVariables (rule_getInputTerm rule) in 
	let programVars = term_getExpressionVariables termDecl (rule_getInputTerm rule) in 
	let checkPremises varsToCheck premise = 
		formula_isPredicate typing premise && 
		List.mem (formula_getFirstInputUpToApp premise) varsToCheck in  (* it checks premises use the right predicates and only the vars from the conclusion  *)
	let checkProgramIsTyped oneVar = List.exists (checkPremises [oneVar]) (rule_getPremises rule) in 
	ck (rule_isPredicate typing rule) ("rule not in WF2: the rule is not a typing rule") &&
	ck (List.for_all (checkPremises vars) (rule_getPremises rule)) ("rule not in WF1: all premises must be typing rules and type variables in the input : " ^ generateRule rule) && 
	ck (List.for_all checkProgramIsTyped programVars) ("rule not in WF2: all program variables must be assigned a type : " ^ (String.concat "" (List.map generateTerm programVars))) 

let type_check_typingRuleForConstructor termDecl typename rule = 
	ck (term_isSkeletonFor (term_getOperator termDecl) (rule_getInputTerm rule)) ("type_check_typingRuleForConstructor: typing rule does not type a skeleton of the expected type") && 
	rule_wellFormed2 termDecl rule && 
	ck (term_isSkeletonFor typename (rule_getOutputTerm rule)) ("type_check_typingRuleForConstructor: typing rule does not type a skeleton of the expected type")
	
let type_check_typingRuleForEliminator termDecl typename rule = 
	let premises = rule_getPremises rule in 
	let vars = term_getExpressionVariables termDecl (rule_getInputTerm rule) in 
	ck (term_isSkeletonFor (term_getOperator termDecl) (rule_getInputTerm rule)) ("type_check_typingRuleForEliminator: typing rule does not type a skeleton of the expected type") &&  
	rule_wellFormed2 termDecl rule && 
	ck (not(vars = [])) "type_check_typingRuleForEliminator: operator does not seem to contain any arguments, cannot be eliminator"  (* at least the eliminating argument should be there *)	
	(* here I have removed a check that the typing rule would assign a constructed type to the eliminating argument. ensured by the classification *)
	
let type_check_typingRuleForDerived termDecl rule = 
	let vars = term_getExpressionVariables termDecl (rule_getInputTerm rule) in 
	ck (term_isSkeletonFor (term_getOperator termDecl) (rule_getInputTerm rule)) ("type_check_typingRuleForDerived: typing rule does not type a skeleton of the expected type") &&  
	rule_wellFormed2 termDecl rule && 
	ck (not(vars = [])) "type_check_typingRuleForEliminator: operator does not seem to contain any arguments, cannot be eliminator"   (* at least the eliminating argument should be there *)	

let type_check_typingRuleError termDecl rule = 
	ck (term_isSkeletonFor (term_getOperator termDecl) (rule_getInputTerm rule)) ("type_check_typingRuleError: typing rule does not type a skeleton of the error") &&  
	rule_wellFormed2 termDecl rule && 
	ck (term_isFreeVar rule (rule_getOutputTerm rule)) ("type_check_typingRuleError: typing rule for error does not type error at ANY type T")

let type_check_reductionRule termDecl rule = 
	let ctx = term_getContextInfo termDecl in 
	ck (term_isSkeletonMayNestFor (term_getOperator termDecl) (rule_getInputTerm rule)) ("type_check_reductionRule: the rule is not defined for skeleton of operators") &&  
	ck (rule_isPredicate reduction rule) "type_check_reductionRule: reduction does not define a predicate step" && 
	rule_wellFormed1 rule &&
	ck (list_subset (snd (positionsCheckedForValuehood rule)) (term_getContextualPositions termDecl)) "type_check_reductionRule: arguments checked for valuehood are not contextual" (* arguments checked for valuehood by reductions rules are contextual *)
		
let type_check_constructors typename termSpec = 
	let termDecl = specTerm_getSig termSpec in 
	let ctx = term_getContextInfo termDecl in 
	type_check_typingRuleForConstructor (specTerm_getSig termSpec) typename (specTerm_getTyping termSpec) &&
	ck (specTerm_getReduction termSpec = []) "type_check_constructors: spotted reduction rules for a constructor. " && (* i.e. no reduction rules for constructors *) 
	ck (list_subset (term_getValPositions termDecl) (term_getContextualPositions termDecl)) "type_check_constructors: the arguments that require valuehood to form a value are not contextual" && (* i.e. the arguments that require valuehood are contextual *)
	ck (ctx_isMonotonic ctx) "type_check_constructors: evaluation contexts contain cyclic dependencies."

let type_check_eliminators typename listOfConstructors termSpec = 
	let ctx = term_getContextInfo (specTerm_getSig termSpec) in 
	type_check_typingRuleForEliminator (specTerm_getSig termSpec) typename (specTerm_getTyping termSpec)  &&
	List.for_all (type_check_reductionRule (specTerm_getSig termSpec)) (specTerm_getReduction termSpec) &&
	ck (List.for_all (rule_checkEliminates listOfConstructors) (specTerm_getReduction termSpec)) ("type_check_eliminators: eliminator eliminates something that is not one of its values" ^ (String.concat "-" listOfConstructors) ^ (String.concat "\n" (List.map generateRule (specTerm_getReduction termSpec)))) &&
	ck (List.for_all (rule_checkEliminatesAll (specTerm_getReduction termSpec)) listOfConstructors) ("type_check_eliminators: not all values are eliminated" ^ (String.concat "-" listOfConstructors) ^ (String.concat "\n" (List.map generateRule (specTerm_getReduction termSpec)))) &&
	ck (List.mem 1 (List.map fst ctx)) "type_check_eliminators: the eliminating argument is not declared as contextual" && (* i.e. the eliminating argument is declared as contextual *)
	ck (ctx_isMonotonic ctx) "type_check_eliminators: evaluation contexts contain cyclic dependencies."

let type_check_errorHandler errordDecl termSpec = 
	let ctx = term_getContextInfo (specTerm_getSig termSpec) in 
	type_check_typingRuleForDerived (specTerm_getSig termSpec) (specTerm_getTyping termSpec) &&
	List.for_all (type_check_reductionRule (specTerm_getSig termSpec)) (specTerm_getReduction termSpec) &&
	ck (List.exists (rule_checkEliminates [term_getOperator errordDecl]) (specTerm_getReduction termSpec)) "type_check_errorHandler: error handler does not eliminate the error" &&
	(* Here you should check that the error handler has a reduction rule for a variable at eliminating argument *)
	ck (List.mem 1 (List.map fst ctx)) "type_check_errorHandler: the eliminating argument that handles the error is not declared as contextual" && (* i.e. the eliminating argument that handles the error is declared as contextual *)
	ck (ctx_isMonotonic ctx) "type_check_errorHandler: evaluation contexts contain cyclic dependencies."

let typecheck_errors errorSpec = 
	if is_none errorSpec then true else 
	let errorTermSpec = (specError_getError errorSpec) in 
	let errordDecl = specTerm_getSig errorTermSpec in 
	let ctx = term_getContextInfo errordDecl in 
	type_check_typingRuleError errordDecl (specTerm_getTyping errorTermSpec) &&
	List.for_all (type_check_errorHandler errordDecl) (specError_getHandlers errorSpec) &&
	ck (specTerm_getReduction errorTermSpec = []) "typecheck_errors: spotted reduction rules for the error. " && 
	ck (list_subset (term_getValPositions errordDecl) (term_getContextualPositions errordDecl)) "typecheck_errors: the arguments that require valuehood are not contextual" && (* i.e. the arguments that require valuehood are contextual *)
	ck (ctx_isMonotonic ctx) "typecheck_errors: evaluation contexts contain cyclic dependencies."

let typecheck_typeSpec typeSpec = 
	let typename = type_getOperator (specType_getSig typeSpec) in 
	List.for_all (type_check_constructors typename) (specType_getConstructors typeSpec) &&
	List.for_all (type_check_eliminators typename (specType_getConstructorsNAMES typeSpec)) (specType_getEliminators typeSpec) 

let typecheck_derivedSpec termSpec = 
	type_check_typingRuleForDerived (specTerm_getSig termSpec) (specTerm_getTyping termSpec) &&
	List.for_all (type_check_reductionRule (specTerm_getSig termSpec)) (specTerm_getReduction termSpec) 
	
let typecheck_ldl ldl = 
	ck 	(List.for_all typecheck_typeSpec (ldl_getTypes ldl) && List.for_all typecheck_derivedSpec (ldl_getDerived ldl) && typecheck_errors (ldl_getError ldl))
		("The Safe Typed language is not ok. " ^ String.concat "-" (List.concat (List.map specType_getConstructorsNAMES (ldl_getTypes ldl))))
	
