
open Batteries
open String
open Option
open Aux
open TypedLanguage
open Ldl
open GenerateLambdaProlog
open Subtyping
open ListManagement

let rec premiseTransformation allPremises applicationsInConclusion formula = match formula with
         | Formula(pred, inputs, outputs) -> 
			 (let subject = formula_getFirstInputUpToApp (Formula(pred, inputs, outputs))  in 
			 try 
			   (let applied = (List.assoc subject applicationsInConclusion) in 
			    let linkedVariables = List.map fst (term_retrieveApplications (formula_getLastArgument formula)) in 
			    let linkedToApplyTmp = (List.map (premiseTransformationToLinked allPremises applied) linkedVariables) in 
				let linkedPremises = List.concat (List.map get3_1 linkedToApplyTmp) in 
				let linkedChecks = List.concat (List.map get3_2 linkedToApplyTmp) in 
			   (Formula(pred, List.map (term_substitutions [Bound "x", applied]) inputs, List.map (term_substitutions [Bound "x", applied]) outputs) :: linkedPremises, linkedChecks, Some applied))
		      with Not_found -> ([Formula(pred, inputs, outputs)], [],  None))
         | Hypothetical(formula1, formula2) -> 
			 let (newPremises, newChecks, var) = premiseTransformation allPremises applicationsInConclusion formula2 in 
			 if is_none var 
				 then ([Hypothetical(formula1, formula2)], [], None)
		 		 else (newPremises, formula_substitutions [Bound "x", get var] formula1 :: newChecks, var)
         | Generic(formula) -> 
			 let (newPremises, newChecks, var) = premiseTransformation allPremises applicationsInConclusion formula in 
			 if is_none var 
				 then ([Generic(formula)], [], None)
		 		 else (newPremises, newChecks, var)			 
and premiseTransformationToLinked allPremises applied var = 
	let tmpRule = (Rule("", allPremises, Formula("", [], []))) in
	match rule_lookup_premise_by_var tmpRule var with (* this is the type requested by the substituted *)
		| None -> ([], [], None)
		| Some index -> 
			let allPremisesWithThatRemoved = list_deleteAt allPremises (index -1) in (* raise(Failure(String.concat "==" (list_deleteAt ["uno" ; "due" ; "tre" ; "quattro"] 2))) in *)
			 premiseTransformation allPremisesWithThatRemoved [(var, applied)] (nthMinusOne allPremises index) 
	
let formula_popListAccessIfAny premisesOfTypingRule reductionRule firstLevelTerm = 
	(* when it comes to the nested record, we do not do inversion on the typing rules for records. i.e. empty + cons ..  *)
	(* this means that we have here to do the instantiation of the typing rule for the elimination rule *)
	let fail = (([],[]), premisesOfTypingRule) in 
	let successUpdate premise = match premise with (Formula(_, inputs, outputs)) ->
		match (inputs @ outputs) with [listt ; l ; e ; listt2] -> match premisesOfTypingRule with (typeRecord :: lookup :: rest) -> 
			let t = formula_getLastArgument lookup in 
			let record = term_getConstructor (List.hd (term_getArguments (rule_getInputTerm reductionRule))) in 
			let typeabilityDerived = formula_putInInput typeRecord (Constructor(record, [listt2])) in 
			let typeabilityToCheck = formula_putInInput typeRecord (Constructor(record, [listt])) in 
			let typeOfPremise = toTypeOfPremise e t in 
				(([typeabilityDerived ; premise], [typeabilityToCheck ; lookup ; premise ; typeOfPremise]) , premisesOfTypingRule) in 
	let successLookup premise = match premise with (Formula(_, inputs, outputs)) -> 
		match (inputs @ outputs) with [listt2 ; l ; e] -> match premisesOfTypingRule with (typeRecord :: lookup :: rest) -> 
			let t = formula_getLastArgument lookup in 
			let record = term_getConstructor (List.hd (term_getArguments (rule_getInputTerm reductionRule))) in 
			let typeabilityDerived = toTypeOfPremise e t in 
			let typeabilityToCheck = typeRecord in
				(([typeabilityDerived ; premise], [typeabilityToCheck ; lookup ; premise]) , premisesOfTypingRule) in 
	match rule_getPremises reductionRule with 
	 | (premise :: rest) -> let pred = formula_getPredicate premise in if String.ends_with pred "_update" then successUpdate premise else if String.ends_with pred "_member" then successLookup premise else fail 
	 | _ -> fail 
	 
let testsAsRules_byReductionRuleEliminator elimBool errorBool subtyping listConstructorsSpec typingRule reductionRule = 
	let rulename = "test_" ^ rule_getRuleName reductionRule in 
	let firstLevelTerm = (rule_getInputTerm reductionRule) in 
	let associations = List.combine (term_getArguments firstLevelTerm) (term_getArguments (rule_getInputTerm typingRule)) in
	let reductionRule = rule_substitutions associations reductionRule in 
	let newConclusion = rule_addOutputFromTypingRule typingRule (rule_outputBecomesInput (rule_turnFormulaTo typing (rule_getConclusion reductionRule))) in
	let applicationsInConclusion = term_retrieveApplications (rule_getOutputTerm reductionRule) in
	let premisesOfTypingRule = (rule_getPremises typingRule) in 
	let triplesFirst = (List.map (premiseTransformation (rule_getPremises typingRule) applicationsInConclusion) premisesOfTypingRule) in 
	let premisesFirst = List.concat (List.map get3_1 triplesFirst) in 
	let checksFirst = List.concat (List.map get3_2 triplesFirst) in 
	if not(elimBool) then (Rule(rulename, premisesFirst, newConclusion), checksFirst) else 
	let secondLevelTerm = (List.hd (term_getArguments (rule_getInputTerm reductionRule))) in 
	(* This below instantiates the principal argument of the typing rule with  the  *)
	let premisesOfTypingRule = (formula_putInInput (List.hd premisesOfTypingRule) secondLevelTerm) :: (List.tl premisesFirst) in 
	let triplesFirst = (List.map (premiseTransformation (rule_getPremises typingRule) applicationsInConclusion) premisesOfTypingRule) in 
	let premisesFirst = List.concat (List.map get3_1 triplesFirst) in 
	let checksFirst = List.concat (List.map get3_2 triplesFirst) in 
	(* pairWithListFactAndGoal contains a pair with the inversion (as lists) for list member or list update, and the formulae to check then *)
	let (pairWithListFactAndGoal, premisesOfTypingRule) = formula_popListAccessIfAny premisesOfTypingRule reductionRule firstLevelTerm in 
	if not(listConstructorsSpec = []) && termDecl_isList (specTerm_getSig (List.hd listConstructorsSpec)) then (Rule(rulename, premisesFirst @ (fst pairWithListFactAndGoal), newConclusion), checksFirst @ (snd pairWithListFactAndGoal)) else 
	let eliminatedConstructor = term_getConstructor secondLevelTerm in 
	let search = List.filter (fun termSpec -> specTerm_getOperator termSpec = eliminatedConstructor) listConstructorsSpec in
	let termSpecConstructor = if search = [] then raise(Failure "testsAsRules_byReductionRuleEliminator: Eliminated operators is not in the list of constructors.") else List.hd search in 
	let typingRuleEliminated = specTerm_getTyping termSpecConstructor in 
	let whatToFeedForTheSecond = 
  			(if is_none subtyping 
				then rule_getPremises typingRuleEliminated
				else
	  			  if errorBool 
					  then fst (inversion_error termSpecConstructor)
			  		  else 
						  let (typ, invPremises, _) = (inversion_typing (subtyping_getRules subtyping) termSpecConstructor) in 
					  	  let typassociations = List.combine (term_getArguments typ) (term_getArguments (formula_getFirstOutput (List.hd premisesFirst))) in
						  let invPremisesSubstituted = List.map (formula_substitutions typassociations) invPremises in 
					  	  let (invPremisesNoEqualities, equalitiesAsFormulae) = pop_out_equalities invPremisesSubstituted in 
					  	  let equalities = List.map fromEqualityToSubstitution equalitiesAsFormulae in 
					  	   List.map (formula_substitutions equalities) invPremisesNoEqualities) in 						  
	let triplesSecond = (List.map (premiseTransformation whatToFeedForTheSecond applicationsInConclusion) whatToFeedForTheSecond) in 
	let premisesSecond = List.concat (List.map get3_1 triplesSecond) in 
	let checksSecond = List.concat (List.map get3_2 triplesSecond) in 
	 (Rule(rulename, premisesFirst @ premisesSecond, newConclusion), checksFirst @ checksSecond) 
							
let testsAsRules_eliminators subtyping listConstructorsSpec termSpec = List.map (testsAsRules_byReductionRuleEliminator true false subtyping listConstructorsSpec (specTerm_getTyping termSpec)) (specTerm_getReduction termSpec)

let testsAsRules_byPlainRule typingRule reductionRule = testsAsRules_byReductionRuleEliminator false true None [] typingRule reductionRule

let testsAsRules_byReductionRuleErrorHandlers subtyping listConstructorsSpec typingRule reductionRule = 
	if rule_checkFreeReduction reductionRule then testsAsRules_byPlainRule typingRule reductionRule else testsAsRules_byReductionRuleEliminator true true subtyping listConstructorsSpec typingRule reductionRule

let testsAsRules_errorHandlers subtyping listConstructorsSpec termSpec = List.map (testsAsRules_byReductionRuleErrorHandlers subtyping listConstructorsSpec (specTerm_getTyping termSpec)) (specTerm_getReduction termSpec)

let testsAsRules_types subtyping typeSpec = List.concat (List.map (testsAsRules_eliminators subtyping (specType_getConstructors typeSpec)) (specType_getEliminators typeSpec))
let testsAsRules_derived termSpec = List.map (testsAsRules_byPlainRule (specTerm_getTyping termSpec)) (specTerm_getReduction termSpec)
let testsAsRules_error subtyping errorSpec = List.concat (List.map (testsAsRules_errorHandlers subtyping [(specError_getError errorSpec)]) (specError_getHandlers errorSpec))
 
let preservationTestsAsRules ldl subtyping = 
	List.concat (List.map (testsAsRules_types subtyping) (ldl_getTypes ldl)) @
	List.concat (List.map testsAsRules_derived (ldl_getDerived ldl)) @
	if ldl_containErrors ldl then testsAsRules_error subtyping (ldl_getError ldl) else []


