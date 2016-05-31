
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open LdlToTypedLanguage
open Proof
open GenerateLambdaProlog

let rule_hypothetical tl rule abs_index = 
	let term = rule_getInputTerm rule in 
	let targetConstructor = if index_fst abs_index = 1 then term_getConstructor term else try (term_getConstructor (List.hd (term_getArguments term))) with Failure _ ->  raise(Failure(rule_getRuleName rule))  in 
	let typingrule = (try List.hd (List.filter (rule_isPredicateAndName typing targetConstructor) (tl_getRules tl)) with Failure _ ->  raise(Failure(rule_getRuleName rule))) in 
	let targetVar = List.nth (term_getArguments (rule_getInputTerm typingrule)) (index_sndReal abs_index) in 
		List.exists (fun premise -> formula_getFirstInputUpToApp premise = targetVar && formula_isHypothetical premise) (rule_getPremises typingrule) 

let getSignaturesForContextualMovers ldl butOnlyErrorContexts = 
	let signatureConstructors = List.map specTerm_getSig (List.concat (List.map specType_getConstructors (ldl_getTypes ldl))) in 
	let signatureEliminators = List.map specTerm_getSig (List.concat (List.map specType_getEliminators (ldl_getTypes ldl))) in 
	let signatureDerived = (List.map specTerm_getSig (ldl_getDerived ldl)) in 
	let signatureError = if ldl_containErrors ldl then [specTerm_getSig (specError_getError (ldl_getError ldl))] else [] in 
	let signatureErrorHandlers = if ldl_containErrors ldl then (List.map specTerm_getSig (specError_getHandlers (ldl_getError ldl))) else [] in 
	let alsoThoseForErrorsIfNeeded = if butOnlyErrorContexts then [] else signatureErrorHandlers in  
	 signatureConstructors @ signatureEliminators  @ signatureDerived  @ alsoThoseForErrorsIfNeeded @ signatureError

let substitutionLemma ldl rule = 
	let tl = compile ldl in (* Just to easily retrieve rules/declarations *)
	let toArg index = "Arg" ^ (string_of_int (index_fst index)) ^ "_" ^ (string_of_int (1 + (index_snd index))) in 
	let instAndCut (abs_index, app_index, applied) = 
		(if rule_hypothetical tl rule abs_index then 
			if term_isVar applied 
				then Tactic(InstAndCut(toArg abs_index, toString applied, toArg app_index)) 
				else 	let op = if index_fst abs_index == 1 then term_getConstructor (rule_getInputTerm rule) else term_getNestedFirstArgument (rule_getInputTerm rule) in 
						let typingruleOp = List.hd (List.filter (rule_isPredicateAndName typing op) (ldl_getAllRules ldl)) in 
						let typOfApplied = formula_getHypotheticalPart (List.nth (rule_getPremises typingruleOp) (index_snd abs_index)) in 
						 Seq([Tactic(Named("Cutting", Assert("{" ^ generateFormula (toTypeOfPremise  applied typOfApplied) ^ "}"))) ; Tactic(InstAndCut(toArg abs_index, toString applied, "Cutting"))]) 
		else Tactic(Inst(toArg abs_index, toString applied))) in 
	List.map instAndCut (List.map (term_toPosition tl (rule_getInputTerm rule)) (term_retrieveApplications (rule_getOutputTerm rule)))

let singleDestruction = [Tactic(Named("Arg1_1", CaseKeep("TypeOf")))]
let doubleDestruction = [Tactic(Named("Arg1_1", CaseKeep("TypeOf"))) ; Tactic(Named("Arg2_1", CaseKeep("Arg1_1")))]

let subProof ldl destructionCases rule = 
	Seq(destructionCases @ substitutionLemma ldl rule @ [Tactic(Search)])
		
let subProofErrorHandler ldl rule = 
	if rule_checkEliminatesSome rule then subProof ldl doubleDestruction rule else subProof ldl singleDestruction rule

let subProofContextual termDecl = 
	let single_line = fun index -> let hypByArgIndex = "TypeOf" ^ (string_of_int index) in Seq([Tactic(Named("TypeOf1", Case("TypeOf"))) ; Tactic(Apply("IH", [hypByArgIndex ; "Step"])) ; Tactic(Search)]) in 
	 List.map single_line (term_getContextualPositions termDecl)		 

let generatePreservationTheorem ldl = 
         let theorem = "Theorem preservation : forall Exp Exp' T, {typeOf Exp T} -> {step Exp Exp'} -> {typeOf Exp' T}." in 
		 let preamble = Seq([Tactic(Induction(2)) ; Tactic(Intros(["TypeOf" ; "Main"])) ; Tactic(Named("Step", Case("Main")))]) in
		 let proofEliminators = List.map (subProof ldl doubleDestruction) (List.filter rule_isReductionRule (ldl_getRulesOfEliminators (ldl_getTypes ldl))) in 
		 let proofDerived = List.map (subProof ldl singleDestruction) (List.filter rule_isReductionRule (List.concat (List.map specTerm_getRules (ldl_getDerived ldl)))) in 
		 let proofErrorHandlers = if ldl_containErrors ldl then List.map (subProofErrorHandler ldl) (List.filter rule_isReductionRule (List.concat (List.map specTerm_getRules (specError_getHandlers (ldl_getError ldl))))) else [] in 
         let allSignaturesForContextualMovers = getSignaturesForContextualMovers ldl false in 
		 let proofContextual = List.concat (List.map subProofContextual allSignaturesForContextualMovers) in
         let allSignaturesForErrorContextualMovers = getSignaturesForContextualMovers ldl true in 
		 let proofErrorContexts = if (ldl_containErrors ldl) then List.map (fun tactic -> Seq([Tactic(Case("Step")) ; Tactic(Named("TypeOf1", Case("TypeOf"))) ; tactic ; Tactic(Search)])) (List.map (toCaseTactic "TypeOf") (List.concat (List.map term_getContextualPositions allSignaturesForErrorContextualMovers))) else [] in 
            Theorem(theorem, Seq( (preamble::proofEliminators) @ proofDerived @ proofErrorHandlers @ proofContextual @ proofErrorContexts))
			
			
			(* (seekDeclTermOf signatureTerms canonical_c)
		List.map2 (subProofReductionPerCanonical termDecl) canonicalDecls (List.map (rule_seekStepOfWith c rules) canonicalDecls)) 
	let premise = (List.filter (fun premise -> formula_getFirstInputUpToApp premise = targetVar) (rule_getPremises typingrule)) in 
	if premise = [] then raise(Failure(rule_getRuleName rule)) else 
		match List.hd premise with Hypothetical(term1, term2, term3) -> true | otherwise -> false
			
			[Tactic(Case(term_getOperator termDecl)) ; 
	if (List.length signatureErrors) > 1 then raise(Failure ("2 error handlers: " ^ (String.concat "-" (List.map term_getOperator signatureErrorHandlers)))) else
			
				Algorithm for reduction rules:
				case on destructive argument, create a substitution lemma for the other arguments if hypothetical. If no destruction of a type, then the proof is done with search. 
				  if instead, the operator destruct a type, then we case again on the first argument which is the nested operator. Now, create a substitution lemma for ALL the arguments if hypothetical (including the first of the nested). Conclude with search. 				
			*)