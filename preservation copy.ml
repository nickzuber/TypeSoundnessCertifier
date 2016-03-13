
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open SafeToTyped
open Proof

let rule_hypothetical sl rule abs_index = 
	let term = rule_getInputTerm rule in 
	let targetConstructor = if fst abs_index = 1 then term_getConstructor term else try (term_getConstructor (List.hd (term_getArguments term))) with Failure _ ->  raise(Failure(rule_getRuleName rule))  in 
	let typingrule = (try List.hd (List.filter (rule_isPredicateAndName typing targetConstructor) (tl_getRules (compile sl))) with Failure _ ->  raise(Failure(rule_getRuleName rule))) in 
	let targetVar = List.nth (term_getArguments (rule_getInputTerm typingrule)) (snd abs_index) in 
		List.exists (fun premise -> formula_getFirstInputUpToApp premise = targetVar && formula_isHypothetical premise) (rule_getPremises typingrule) 

let getSignaturesForContextualMovers sl butOnlyErrorContexts = 
	let signatureConstructors = List.map specTerm_getSig (List.concat (List.map specType_getConstructors (sl_getTypes sl))) in 
	let signatureEliminators = List.map specTerm_getSig (List.concat (List.map specType_getEliminators (sl_getTypes sl))) in 
	let signatureOthers = (List.map specTerm_getSig (sl_getOthers sl)) in 
	let signatureError = if sl_containErrors sl then [specTerm_getSig (specError_getError (sl_getError sl))] else [] in 
	let signatureErrorHandlers = if sl_containErrors sl then (List.map specTerm_getSig (specError_getHandlers (sl_getError sl))) else [] in 
	let alsoThoseForErrorsIfNeeded = if butOnlyErrorContexts then [] else signatureErrorHandlers in  
	 signatureConstructors @ signatureEliminators  @ signatureOthers  @ alsoThoseForErrorsIfNeeded @ signatureError

let substitutionLemma sl rule = 
	let toArg (index1, index2) = "Arg" ^ (string_of_int index1) ^ "_" ^ (string_of_int (1 + index2)) in 
	let instAndCut (abs_index, app_index, applied) = if rule_hypothetical sl rule abs_index then Tactic(InstAndCut(toArg abs_index, applied, toArg app_index)) else Tactic(Inst(toArg abs_index, applied)) in 
	List.map instAndCut (List.map (term_toPosition (rule_getInputTerm rule)) (term_retrieveApplications (rule_getOutputTerm rule)))

let singleDestruction = [Tactic(Named("Arg1_1", CaseKeep("TypeOf")))]
let doubleDestruction = [Tactic(Named("Arg1_1", CaseKeep("TypeOf"))) ; Tactic(Named("Arg2_1", CaseKeep("Arg1_1")))]

let subProof sl destructionCases rule = 
	Seq(destructionCases @ substitutionLemma sl rule @ [Tactic(Search)])
		
let subProofErrorHandler sl rule = 
	if rule_checkEliminatesSome rule then subProof sl doubleDestruction rule else subProof sl singleDestruction rule

let subProofContextual termDecl = 
	let single_line = fun index -> let hypByArgIndex = "TypeOf" ^ (string_of_int index) in Seq([Tactic(Named("TypeOf1", Case("TypeOf"))) ; Tactic(Apply("IH", [hypByArgIndex ; "Step"])) ; Tactic(Search)]) in 
	 List.map single_line (term_getContextualPositions termDecl)		 

let generatePreservationTheorem sl = 
         let theorem = "Theorem preservation : forall E E' T, {typeOf E T} -> {step E E'} -> {typeOf E' T}." in 
		 let preamble = Seq([Tactic(Induction(2)) ; Tactic(Intros(["TypeOf" ; "Main"])) ; Tactic(Named("Step", Case("Main")))]) in
		 let proofEliminators = List.map (subProof sl doubleDestruction) (List.filter rule_isReductionRule (sl_getReductionRulesOfEliminators (sl_getTypes sl))) in 
		 let proofOthers = List.map (subProof sl singleDestruction) (List.filter rule_isReductionRule (List.concat (List.map specTerm_getRules (sl_getOthers sl)))) in 
		 let proofErrorHandlers = if sl_containErrors sl then List.map (subProofErrorHandler sl) (List.filter rule_isReductionRule (List.concat (List.map specTerm_getRules (specError_getHandlers (sl_getError sl))))) else [] in 
         let allSignaturesForContextualMovers = getSignaturesForContextualMovers sl false in 
		 let proofContextual = List.concat (List.map subProofContextual allSignaturesForContextualMovers) in
         let allSignaturesForErrorContextualMovers = getSignaturesForContextualMovers sl true in 
		 let proofErrorContexts = if (sl_containErrors sl) then List.map (fun tactic -> Seq([Tactic(Case("Step")) ; Tactic(Named("TypeOf1", Case("TypeOf"))) ; tactic ; Tactic(Search)])) (List.map (toCaseTactic "TypeOf") (List.concat (List.map term_getContextualPositions allSignaturesForErrorContextualMovers))) else [] in 
            Theorem(theorem, Seq( (preamble::proofEliminators) @ proofOthers @ proofErrorHandlers @ proofContextual @ proofErrorContexts))
			
			
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