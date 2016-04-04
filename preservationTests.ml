
open Batteries
open Aux
open TypedLanguage
open SafeTypedLanguage

let sameapplication applicationsInConclusion term1 term2 = match (term1, term2) with 
	| (Application(var1, sameTerm1), Application(var2, sameTerm2)) -> if toString sameTerm1 = toString sameTerm2 then (try [var2, (List.assoc var1 applicationsInConclusion)] with Not_found -> [var1, (List.assoc var2 applicationsInConclusion)]) else raise(Failure("the else case: " ^ toString term1 ^ toString term2))	
	| _ -> raise(Failure("the _ case: " ^ toString term1 ^ toString term2))	(* this used to be [] and also the else above. *)				
	
let rec term_substitutions associations term = match term with
         | Var(variable) -> (try (List.assoc (Var(variable)) associations) with Not_found -> (Var(variable)))
         | Application(term1,term2) -> Application(term_substitutions associations term1, term_substitutions associations term2)
         | Constructor(c,args) -> Constructor(c,List.map (term_substitutions associations) args)

		 
let term_apply applicationsInConclusion term = match term with
	| Application(term1,term2) -> 
		if term_isBound term2 
			then let term2substituted = (try (List.assoc term1 applicationsInConclusion) with Not_found -> Var((toString term1) ^ "X" )) in Application(term1,term2substituted)
			else Application(term1,term2)
	| otherwise -> otherwise
		
let premiseTransformation associations applicationsInConclusion formula = match formula with
         | Formula(pred, inputs, outputs) -> Formula(pred, (List.map (term_apply applicationsInConclusion) (List.map (term_substitutions associations) inputs)), (List.map (term_apply applicationsInConclusion) (List.map (term_substitutions associations) outputs))) 
         | Hypothetical(typ1,term,typ2) -> 
			 if List.exists (fun x -> List.mem_assoc x applicationsInConclusion) (term_getVariables term)
				then Formula("typeOf", [term_apply applicationsInConclusion (term_substitutions associations term)], [typ2])
		 		else Hypothetical(term_substitutions associations typ1,term_substitutions associations term,term_substitutions associations typ2)
         | Generic(term1,term2) -> match (sameapplication applicationsInConclusion term1 term2) with 
		 		| [] -> Formula("typeOf", [term_apply applicationsInConclusion (term_substitutions associations term1)], [term_apply applicationsInConclusion (term_substitutions associations term2)])
				| [variable1,applied] -> let applicationsInConclusion2 = (variable1, applied)::applicationsInConclusion in Formula("typeOf", [term_apply applicationsInConclusion2 (term_substitutions associations term1)], [term_apply applicationsInConclusion2 (term_substitutions associations term2)])

let testsAsRules_commoncase typingRule reductionRule focusedTerm = 
	let rulename = "test_" ^ rule_getRuleName reductionRule in 
	let associations = List.combine (term_getArguments (rule_getInputTerm typingRule)) (term_getArguments focusedTerm) in
	let applicationsInConclusion = term_retrieveApplications (rule_getOutputTerm reductionRule) in
	let newPremises = List.map (premiseTransformation associations applicationsInConclusion) (rule_getPremises typingRule) in 
	let newConclusion = rule_addOutputFromTypingRule typingRule (rule_outputBecomesInput (rule_turnFormulaTo typing (rule_getConclusion reductionRule))) in
		Rule(rulename, newPremises, newConclusion) 

let testsAsRules_byReductionRule typingRule reductionRule = testsAsRules_commoncase typingRule reductionRule (rule_getInputTerm reductionRule)
	
let testsAsRules_byReductionRuleEliminator listConstructorsSpec typingRule reductionRule = 
	let firstLevelTerm = (rule_getInputTerm reductionRule) in 
	let ruleWithFirstLevel = testsAsRules_commoncase typingRule reductionRule firstLevelTerm in
	let eliminatedConstructor = term_getConstructor (List.hd (term_getArguments (rule_getInputTerm reductionRule))) in 
	let typingRuleEliminated = let search = List.filter (fun termSpec -> specTerm_getOperator termSpec = eliminatedConstructor) listConstructorsSpec in if search = [] then raise(Failure "testsAsRules_byReductionRuleEliminator: Eliminated operators is not in the list of constructors.") else specTerm_getTyping (List.hd search) in 
	let secondLevelTerm = try List.hd (term_getArguments firstLevelTerm) with Failure e -> raise(Failure "testsAsRules_byReductionRuleEliminator: failed in grabbing the eliminated term") in 
	let ruleWithSecondLevel = testsAsRules_commoncase typingRuleEliminated reductionRule secondLevelTerm in 
		rule_addPremises (rule_getPremises ruleWithSecondLevel) ruleWithFirstLevel
		
let testsAsRules_eliminators listConstructorsSpec termSpec = List.map (testsAsRules_byReductionRuleEliminator listConstructorsSpec (specTerm_getTyping termSpec)) (specTerm_getReduction termSpec)

let testsAsRules_byReductionRuleErrorHandlers listConstructorsSpec typingRule reductionRule = 
	if rule_checkFreeReduction reductionRule then testsAsRules_byReductionRule typingRule reductionRule else testsAsRules_byReductionRuleEliminator listConstructorsSpec typingRule reductionRule

let testsAsRules_errorHandlers listConstructorsSpec termSpec = List.map (testsAsRules_byReductionRuleErrorHandlers listConstructorsSpec (specTerm_getTyping termSpec)) (specTerm_getReduction termSpec)

let testsAsRules_types typeSpec = List.concat (List.map (testsAsRules_eliminators (specType_getConstructors typeSpec)) (specType_getEliminators typeSpec))
let testsAsRules_others termSpec = List.map (testsAsRules_byReductionRule (specTerm_getTyping termSpec)) (specTerm_getReduction termSpec)
let testsAsRules_error errorSpec = List.concat (List.map (testsAsRules_errorHandlers [(specError_getError errorSpec)]) (specError_getHandlers errorSpec))
 
let preservationTestsAsRules sl = 
	List.concat (List.map testsAsRules_types (sl_getTypes sl)) @
	List.concat (List.map testsAsRules_others (sl_getOthers sl)) @
	if sl_containErrors sl then testsAsRules_error (sl_getError sl) else []

