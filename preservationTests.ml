
open Batteries
open Aux
open Type_system

let addOutputFromTypingRule typingRule formula = match formula with Formula(pred, inputs, outputs) ->
         let finaltype = rule_getInputTerm typingRule in
          Formula(pred, inputs, [finaltype])

let outputBecomesInput formula = match formula with Formula(pred, inputs, outputs) -> Formula(pred, outputs, [])

let sameapplication applicationsInConclusion term1 term2 = match (term1, term2) with 
	| (Application(var1, sameTerm1), Application(var2, sameTerm2)) -> if toString sameTerm1 = toString sameTerm2 then (try [var2, (List.assoc var1 applicationsInConclusion)] with Not_found -> [var1, (List.assoc var2 applicationsInConclusion)]) else []
	| _ -> []							
	
let rec substitutionsTerm associations applicationsInConclusion term = match term with
         | Var(variable) -> (try (List.assoc (Var(variable)) associations) with Not_found -> (Var(variable)))
         | Application(term1,term2) ->  
                  let var1Substituted = (substitutionsTerm associations applicationsInConclusion term1) in
                  let var2lookedUp = (try (List.assoc var1Substituted applicationsInConclusion) with Not_found -> term2) in
                    Application(var1Substituted, var2lookedUp) 
         | _ -> raise (Failure "In substitutionsTerm of generatePreservationTests, I have found that premises do not use simple variables E1, E2, etcetera.")

let substitutionsFormula associations applicationsInConclusion formula = match formula with
         | Formula(pred, inputs, outputs) -> Formula(pred, (List.map (substitutionsTerm associations applicationsInConclusion) inputs), outputs) 
         | Hypothetical(typ1,term,typ2) -> Formula("typeOf", [substitutionsTerm associations applicationsInConclusion term], [typ2])
         | Generic(term1,term2) -> match (sameapplication applicationsInConclusion term1 term2) with 
		 		| [] -> Formula("typeOf", [substitutionsTerm associations applicationsInConclusion term1], [substitutionsTerm associations applicationsInConclusion term2])
				| [variable1,applied] -> let applicationsInConclusion2 = (variable1, applied)::applicationsInConclusion in Formula("typeOf", [substitutionsTerm associations applicationsInConclusion2 term1], [substitutionsTerm associations applicationsInConclusion2 term2])


let flattenTheDoubleApplication signatureTerms typingRules rule = match rule with Rule(name,premises,conclusion) ->
         let Constructor(constructor,arguments) = rule_getInputTerm rule in 
         let Constructor(nestedConstructor, nestedArguments) = List.hd arguments in 
         let applicationsInConclusion = retrieveApplications (rule_getInputTerm rule) in
         let typingRuleForTerm = rule_seekTypeOf constructor typingRules in 
         let associationsForTerm = match rule_getInputTerm typingRuleForTerm with Constructor(constructor2,argumentsTyping) -> List.combine argumentsTyping arguments in
         let newPremisesTerm = List.map (substitutionsFormula associationsForTerm applicationsInConclusion) (rule_getPremises typingRuleForTerm) in
         let typingRuleForNested = rule_seekTypeOf nestedConstructor typingRules in 
         let associationsForNested = match rule_getInputTerm typingRuleForNested with Constructor(constructor3,argumentsTypingNested) -> List.combine argumentsTypingNested nestedArguments in
         let newPremisesNested = List.map (substitutionsFormula associationsForNested applicationsInConclusion) (rule_getPremises typingRuleForNested) in
         let newConclusion = addOutputFromTypingRule typingRuleForTerm (outputBecomesInput (rule_turnFormulaTo "typeOf" conclusion)) in
         let testRule = Rule(name, newPremisesTerm @ newPremisesNested, newConclusion) in
          testRule

		  (* reduction rules are all the step rules minus context rules. They come first.  *)
let rulesForPreservationTests ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let typingRules = (List.filter rule_onlyTypingRules rules) in 
         let reductionRules = List.take ((List.length (List.filter rule_onlyStepRules rules)) - (List.length (List.filter rule_onlyContextRules rules))) (List.filter rule_onlyStepRules rules) in 
         let testsAsRules = List.map (flattenTheDoubleApplication signatureTerms typingRules) reductionRules
          in testsAsRules



