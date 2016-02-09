
open Batteries
open Aux
open TypedLanguage
open SafeTypedLanguage

let sameapplication applicationsInConclusion term1 term2 = match (term1, term2) with 
	| (Application(var1, sameTerm1), Application(var2, sameTerm2)) -> if toString sameTerm1 = toString sameTerm2 then (try [var2, (List.assoc var1 applicationsInConclusion)] with Not_found -> [var1, (List.assoc var2 applicationsInConclusion)]) else []
	| _ -> []							
	
let rec term_substitutions associations term = match term with
         | Var(variable) -> (try (List.assoc (Var(variable)) associations) with Not_found -> (Var(variable)))
         | Application(term1,term2) -> Application(term_substitutions associations term1, term_substitutions associations term2)
         | Constructor(c,args) -> Constructor(c,List.map (term_substitutions associations) args)

let term_apply applicationsInConclusion term = match term with
	| Application(term1,term2) -> let term2substituted = (try (List.assoc term1 applicationsInConclusion) with Not_found -> Var((toString term1) ^ "X" )) in Application(term1,term2substituted)
	| otherwise -> otherwise
		
let premiseTransformation associations applicationsInConclusion formula = match formula with
         | Formula(pred, inputs, outputs) -> Formula(pred, (List.map (term_apply applicationsInConclusion) (List.map (term_substitutions associations) inputs)), (List.map (term_apply applicationsInConclusion) (List.map (term_substitutions associations) outputs))) 
         | Hypothetical(typ1,term,typ2) -> Formula("typeOf", [term_apply applicationsInConclusion (term_substitutions associations term)], [typ2])
         | Generic(term1,term2) -> match (sameapplication applicationsInConclusion term1 term2) with 
		 		| [] -> Formula("typeOf", [term_apply applicationsInConclusion (term_substitutions associations term1)], [term_apply applicationsInConclusion (term_substitutions associations term2)])
				| [variable1,applied] -> let applicationsInConclusion2 = (variable1, applied)::applicationsInConclusion in Formula("typeOf", [term_apply applicationsInConclusion (term_substitutions associations term1)], [term_apply applicationsInConclusion (term_substitutions associations term2)])

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

(*         
	the test:
	newConclusion is:
		- the step, but you switch the output with input and turn step into typeof i.e. step E1 E2 = typeOf E2 E1
		- you replace the output with the output of the typing rule 
	premises:
		you create the association w.r.t. the input of the conclusion of the typing rule with the input of the step. ie. 
				step app (abs R) E AND typeof E1 E2 --> E1 = (abs R), E2 = E. so you will have premises typeOf (abs R) T1->T2, typeOf E T1
				premises.. if you encounter typeOf then you simply substitute. if you encounter hypothetical, you apply with what you have in the conclusion. 
	
	
			 raise (Failure "In substitutionsTerm of generatePreservationTests, I have found that premises do not use simple variables E1, E2, etcetera.")
	
let testsAsRules_byReductionRule typingRule reductionRule = 
	let associations = List.combine (term_getArguments (rule_getInputTerm typingRule)) (term_getArguments (rule_getInputTerm reductionRule)) in
	let applicationsInConclusion = rule_retrieveApplicationsInConclusion (rule_getOutputTerm reductionRule) in
	 List.map premiseTransformation associations applicationsInConclusion (rule_getPremises typingRule)

let testsAsRules_byReductionRule typingRule reductionRule = 
	let rulename = "test_" ^ rule_getRulename reductionRule in 
	let premisesForFirstLevel = testsAsRules_byReductionRule typingRule reductionRule 
	let newConclusion = rule_addOutputFromTypingRule typingRuleForTerm (rule_outputBecomesInput (rule_turnFormulaTo typing conclusion)) in
		Rule(rulename, premisesForFirstLevel, newConclusion) 

let testsAsRules_byReductionRuleEliminator listConstructorsSpec typingRule reductionRule = 
	let rulename = "test_" ^ rule_getRulename reductionRule in 
	let premisesForFirstLevel = testsAsRules_byReductionRule typingRule reductionRule 
	let eliminatedConstructor = ... in 
	let typingRuleEliminated = ... in 
	let premisesForSecondLevel = testsAsRules_byReductionRule typingRuleEliminated reductionRule in 
	let newConclusion = rule_addOutputFromTypingRule typingRuleForTerm (rule_outputBecomesInput (rule_turnFormulaTo typing conclusion)) in
		Rule(rulename, premisesForFirstLevel @ premisesForSecondLevel, newConclusion) 
	
	let Constructor(constructor,arguments) = rule_getInputTerm rule in 
	let Constructor(nestedConstructor, nestedArguments) = List.hd arguments in 
	let applicationsInConclusion = retrieveApplications (rule_getInputTerm rule) in
	let associationsForTerm = match rule_getInputTerm typingRule with Constructor(constructor2,argumentsTyping) -> List.combine argumentsTyping arguments in
	let newPremisesTerm = List.map (substitutionsFormula associationsForTerm applicationsInConclusion) (rule_getPremises typingRule) in
	let typingRuleForNested = rule_seekTypeOf nestedConstructor typingRules in 
	let associationsForNested = match rule_getInputTerm typingRuleForNested with Constructor(constructor3,argumentsTypingNested) -> List.combine argumentsTypingNested nestedArguments in
	let newPremisesNested = List.map (substitutionsFormula associationsForNested applicationsInConclusion) (rule_getPremises typingRuleForNested) in
	
	let typingRules = (List.filter rule_onlyTypingRules rules) in 
         let reductionRules = List.take ((List.length (List.filter rule_onlyStepRules rules)) - (List.length (List.filter rule_onlyContextRules rules))) (List.filter rule_onlyStepRules rules) in 
         let testsAsRules = List.map (flattenTheDoubleApplication signatureTerms typingRules) reductionRules
          in testsAsRules
*)


