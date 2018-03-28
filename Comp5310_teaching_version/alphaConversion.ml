open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open ListManagement

let renameVariablesIfNeededByRule errorHandlerBool ldl subtyping rule = 
	let conclusion = rule_getConclusion rule in 
	if formula_isTyping conclusion 
		then (* typing rule of eliminator must not have its principal arguments containing variables of the typed introduction form  *)
			
			let rulesToSearchIn = 
			
				(if errorHandlerBool 
					then [specTerm_getTyping (specError_getError (ldl_getError ldl))]
					else 
						let typ = term_getConstructor (formula_getFirstOutput (List.hd (rule_getPremises rule))) in (ldl_getRulesOfConstructors [(ldl_lookup_typeSpec ldl typ)])
				 ) in 
			let variablesInAll = removeDuplicates (List.concat (List.map term_getVariables (List.map formula_getFirstInput (List.filter formula_isTyping (List.map rule_getConclusion rulesToSearchIn))))) in 
			let termElim = formula_getFirstInput conclusion in 
			let varsInElim = removeDuplicates (term_getVariables termElim) in 
			let variablesInCommon = list_difference varsInElim (list_difference varsInElim variablesInAll) in 
			let associations = List.combine variablesInCommon (List.map toTicked variablesInCommon) in 
			let newrule = rule_substitutions associations rule in 
			if is_none subtyping  || errorHandlerBool
				then newrule 
				else 
					let variablesInAll = removeDuplicates (List.concat (List.map term_getVariables (List.map formula_getFirstOutput (List.filter formula_isTyping (List.map rule_getConclusion rulesToSearchIn))))) in 
					let varsInElim = removeDuplicates (term_getVariables (formula_getFirstOutput (List.hd (rule_getPremises rule)))) in 
					let variablesInCommon = list_difference varsInElim (list_difference varsInElim variablesInAll) in 
					let associations = List.combine variablesInCommon (List.map toTicked variablesInCommon) in 
					 rule_substitutions associations newrule
			(* PASS 2 about subtyping has been moved: typing rule of eliminator, if we have subtyping then the principal arguments must not have types as in the assigned type of the introduction form  *)
		else (* reduction rule of eliminator, principal argument must be the term in the typing rule *)
		  if not(rule_checkEliminatesSome rule) then rule else 
			let op = rule_getNestedOperatorInEliminationRule rule in 
			let termSpecOfOp = (try (ldl_lookup_constructorTermSpec ldl op) with _ -> ldl_getErrorDeclaration ldl) in
			if termDecl_isList (specTerm_getSig termSpecOfOp) then rule else 
				let typingRuleOp = specTerm_getTyping termSpecOfOp in 
				let termFromTypingRule = rule_getInputTerm typingRuleOp in 
				let termElim = rule_getNestedTermInEliminationRule rule in 
				if termElim = termFromTypingRule then rule else 
					let associations = List.combine (term_getArguments termElim) (term_getArguments termFromTypingRule) in
					 rule_substitutions associations rule

let renameVariablesIfNeeded tl ldl subtyping = 
	let ruleForEliminators = List.concat (List.map specTerm_getRules (ldl_getAllEliminators ldl)) in 
	let ruleForErrorHandlers = if is_none (ldl_getError ldl) then [] else List.concat (List.map specTerm_getRules (specError_getHandlers (ldl_getError ldl))) in 
	let ruleForEliminatorsNEW = List.map (renameVariablesIfNeededByRule false ldl subtyping) ruleForEliminators in 
	let ruleForErrorHandlersNEW = List.map (renameVariablesIfNeededByRule true ldl subtyping) ruleForErrorHandlers in  	
	 tl_setRules tl ((list_difference (list_difference (tl_getRules tl) ruleForEliminators) ruleForErrorHandlers) @ ruleForEliminatorsNEW @ ruleForErrorHandlersNEW)
	
				 
