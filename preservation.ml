
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open ListManagement
open LdlToTypedLanguage
open Proof
open GenerateLambdaProlog
open Subtyping
open ListLemmas

(*
Theorem asd : forall E T1 T2, {typeOf E T1} -> {error E} -> {typeOf E T2}.
Seq([Tactic(Induction(1)) ; Tactic(Intros ["TypeOf", "Error"] ; Tactic(Case("Error")) ; Tactic(Case("TypeOf")) ; Tactic(Case("Search")) ; Tactic(Named("Error", Assert("{error }"))) ; Tactic(Apply("IH", ["H1", "Error"])) ; Tactic(Case("Search"))]))
*)

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


let substitutionLemma ldl runtimeTypingRule formalPremises = 
	let tl = compile ldl in (* Just to easily retrieve rules/declarations *)
	let toArg index = "Hyp" ^ (string_of_int index) in 
	let instAndCutByIndex applied index = 
	(*	if applied = Var("X") then raise(Failure(generateRule runtimeTypingRule ^ String.concat "==" (List.map generateFormula formalPremises)))  else *)
		let premise = nthMinusOne (rule_getPremises runtimeTypingRule) index in 
		let cuttingHyp = "CutHyp" in 
		     if formula_isHypothetical premise 
			   then [Tactic(Named(cuttingHyp, Assert("{" ^ generateFormula (formula_substitutions [(Var("x"), applied)] (formula_getHypotheticalPart premise)) ^ "}"))) ; Tactic(InstAndCut(toArg index, toString applied, cuttingHyp)) ; Tactic(Clear(cuttingHyp)) ; Tactic(Clear("ToCut"))]  
	           else if formula_isGeneric premise then [Tactic(Inst(toArg index, toString applied))] else raise(Failure("Applications are allowed only in hypothetical or generic premises")) in 
	let rec instAndCut applied var = 
		 (match rule_lookup_premise_by_var runtimeTypingRule var with (* this is the type requested by the substituted *)
		 | None -> []
	 	| Some index -> 
			 let selectedPremise = nthMinusOne formalPremises index in 
			 let formalRule = Rule("", formalPremises, List.hd formalPremises) in 
			 (* let otherAbstractions = if (List.map fst (term_retrieveApplications (formula_getFirstOutput premise))) = [] then [] else raise(Failure(generateTerm (formula_getFirstOutput premise) ^ "===" ^ generateRule runtimeTypingRule)) in *)
			 let otherAbstractions = List.map fst (term_retrieveApplications ( try formula_getFirstOutput selectedPremise with _ -> raise (Failure("===" ^ (string_of_int index) ^ (String.concat "-- " (List.map generateFormula formalPremises)))))) in 
			 let indexesOtherAbstractions = List.map get (List.filter is_some (List.map (rule_lookup_premise_by_var formalRule) otherAbstractions)) in 
			   List.concat (List.map (instAndCutByIndex applied) (index::indexesOtherAbstractions))) in 
      List.concat (List.map (fun (var,applied) -> instAndCut applied var) (term_retrieveApplications (rule_getOutputTerm runtimeTypingRule)))
                                                                          (*  here the bound is the number of premises *)
let subProofErrorContextual ldl termDecl = 
	 if ldl_containErrors ldl  
		 then List.map (fun dummyArg -> Tactic(Backchain("error_types", "all"))) (term_getContextualPositions termDecl)		 
 		 else []
		 
let subProofContextual termDecl = 
	let single_line = fun index -> let hypByArgIndex = "Hyp" ^ (string_of_int index) in Seq([Tactic(Apply("IH", [hypByArgIndex ; "Step"])) ; Tactic(Search)]) in 
	let ctxPositions = (term_getContextualPositions termDecl) in 
	 List.map single_line (adjustContextsIfList termDecl ctxPositions)	 

let caseAnalysisOnTyping errorBool termSpec subtyping = 
	let op = specTerm_getOperator termSpec in 
	if is_none subtyping 
		then [Tactic(Named("Hyp1", CaseKeep("Hyp1")))] 
        else 
			let simpleTheorem = (if errorBool then (fst (inversion_error termSpec)) = [] else (get3_2 (inversion_typing (subtyping_getRules subtyping) termSpec)) = []) in 
			if simpleTheorem (* simlpe theorem is FALSE when an inversion_lemmas have premises to deal with, so it will call the inversion_typing_lemma *)
				then [] 
				else [Tactic(Named("Hyp1", Apply(inversion_typing_NAME ^ "_" ^ op, ["Hyp1"])))]
				
let rec subProofConstructor ldl termDecl = 
	let caseForEmptyListIfNeeded = if termDecl_isListButNotSelf termDecl then [Tactic(Named("Step",Case("Step")))] else [] in 
	    Seq(caseForEmptyListIfNeeded @ (Tactic(Named("Step",Case("Step"))) :: subProofContextual termDecl @ subProofErrorContextual ldl termDecl))


let subProofEliminatorByConstructor ldl subtyping termSpec rule = 
	let op = rule_getNestedOperatorInEliminationRule rule in 
	let termSpecConstructor = ldl_lookup_constructorTermSpec ldl op in 
	if termDecl_isList (specTerm_getSig termSpecConstructor) 
		then 
			if rule_doesItUseUpdate_ [rule] op then Seq([Tactic(Apply(op ^ "_" ^ updatePreservationLemma, ["Hyp1" ; "Hyp2" ; "Step" ; "Hyp3"])) ; Tactic(Search)]) else Seq([Tactic(Apply(op ^ "_" ^ memberPreservationLemma, ["Hyp1" ; "Hyp2" ; "Step"])) ; Tactic(Search)])
	else 		
	let typingRule = (specTerm_getTyping termSpec) in 
	let premisesElim = rule_getPremises typingRule in 
	let associationsStep = List.combine (term_getArguments (rule_getInputTerm rule)) (term_getArguments (rule_getInputTerm typingRule)) in 
	let (formalPremisesConstr, premisesConstr) = 
		if is_none subtyping 
			then let premisesToGive = rule_getPremises (specTerm_getTyping termSpecConstructor) in (premisesToGive, premisesToGive) 
			else 
				let typeAsFromElimination = formula_getFirstOutput (List.hd premisesElim) in 
				let subtypingRule = try List.assoc (term_getConstructor typeAsFromElimination) (subtyping_getRules subtyping) with _ -> raise (Failure("no subtyping rule for " ^ op ^ "==" ^ (String.concat "--" (List.map generateRule ((List.map snd (subtyping_getRules subtyping)))))))  in 
(*				let conclusionSub = rule_getConclusion subtypingRule in 
				let [lesser ; greater] = formula_getInputs conclusionSub @ formula_getOutputs conclusionSub in 
*)				
				let inversionInfo = inversion_typing (subtyping_getRules subtyping) termSpecConstructor in 
				let typInvertedByLemma = get3_1 inversionInfo in 
				let premisesFromInversion = get3_2 inversionInfo in 
				let associations = List.combine (term_getArguments typInvertedByLemma) (term_getArguments typeAsFromElimination) in 
				let premisesFromInversionDone = List.map (formula_substitutions associations) premisesFromInversion in 
				let (premisesFromInversionDoneNoEq, equalitiesAsFormulae) = pop_out_equalities premisesFromInversionDone in 
				let equalities = List.map fromEqualityToSubstitution equalitiesAsFormulae in 
				let premisesFromInversionAlsoEq = List.map (formula_substitutions equalities) premisesFromInversionDoneNoEq in 
				let (premisesFromInversionNoEq, _) = pop_out_equalities premisesFromInversion in 
			      (premisesFromInversionNoEq, premisesFromInversionAlsoEq) in 
	let runtimeTypingRule = Rule("", premisesElim @ premisesConstr, formula_substitutions associationsStep (rule_getConclusion rule)) in 
	 Seq(caseAnalysisOnTyping false termSpecConstructor subtyping @ substitutionLemma ldl runtimeTypingRule (premisesElim @ formalPremisesConstr) @ [Tactic(Search)])
	(* raise (Failure (generateRule runtimeTypingRule ^ generateRule typingRule)) *)
     
let subProofEliminator ldl subtyping termSpec = 
	let termDecl = specTerm_getSig termSpec in 
	 Seq([Tactic(Named("Step",Case("Step")))] @ List.map (subProofEliminatorByConstructor ldl subtyping termSpec) (specTerm_getReduction termSpec) @ subProofContextual termDecl @ subProofErrorContextual ldl termDecl)

let subProofDerivedByRule ldl typingRule rule = 
	let premises = rule_getPremises typingRule in 
	let associations = List.combine (term_getArguments (rule_getInputTerm rule)) (term_getArguments (rule_getInputTerm typingRule)) in 
	let runtimeTypingRule = Rule("", premises, formula_substitutions associations (rule_getConclusion rule)) in 	
	  Seq(substitutionLemma ldl runtimeTypingRule premises @ [Tactic(Search)])
	
let subProofDerived ldl termSpec = 
	let typingRule = (specTerm_getTyping termSpec) in 
	let termDecl = specTerm_getSig termSpec in 
	 Seq([Tactic(Named("Step",Case("Step")))] @ List.map (subProofDerivedByRule ldl typingRule) (specTerm_getReduction termSpec) @ subProofContextual termDecl @ subProofErrorContextual ldl termDecl) 

let subProofErrorHandlerByRule ldl subtyping typingRule rule = 
	let premises = rule_getPremises typingRule in 
	let associations = List.combine (term_getArguments (rule_getInputTerm rule)) (term_getArguments (rule_getInputTerm typingRule)) in 
	let runtimeTypingRule = Rule("", premises, formula_substitutions associations (rule_getConclusion rule)) in 	
		if term_isVar (term_getNestedFirstArgument (rule_getInputTerm rule)) 
			then Seq(substitutionLemma ldl runtimeTypingRule premises @ [Tactic(Search)])
			else 
				let op = rule_getNestedOperatorInEliminationRule rule in
				let termSpec = (ldl_getErrorDeclaration ldl) in 
			      Seq(caseAnalysisOnTyping true termSpec subtyping @ substitutionLemma ldl runtimeTypingRule premises @ [Tactic(Search)])

let subProofErrorHandler ldl subtyping termSpec = 
	let typingRule = (specTerm_getTyping termSpec) in 
	let termDecl = specTerm_getSig termSpec in 
	let termDeclForErrorContext = (termDecl_removePrincipalArg_fromContexts termDecl) in (* This removes the principal argument from context info, because that is not in the error contexts. We give temporary termDecl to handle the errorContexts cases *)
	 Seq([Tactic(Named("Step",Case("Step")))] @ List.map (subProofErrorHandlerByRule ldl subtyping typingRule) (specTerm_getReduction termSpec) @ subProofContextual termDecl @ subProofErrorContextual ldl termDeclForErrorContext) 

let error_types_all_NAME = "error_types_all"
let error_types_all_lemma ldl subtyping = 
    if ldl_containErrors ldl 
		then let theorem = "Theorem " ^ error_types_all_NAME ^ ": forall E T1 T2, {typeOf E T1} -> {error E} -> {typeOf E T2}. \n\n" in 
			 if is_none subtyping
				then let preamble = "intros Hyp1 Error. case Error. case Hyp1. \n" in 
				[Theorem(theorem ^ preamble, Tactic(Search))]
				else let preamble = "induction on 1. intros Hyp1 Error. case Error. \n" in 
				[Theorem(theorem ^ preamble, Seq(caseAnalysisOnTyping true (ldl_getErrorDeclaration ldl) subtyping @ [Tactic(Search)]))]
		else []
	 
let generatePreservationTheorem ldl subtyping = 
         let theorem = "Theorem preservation : forall Exp Exp' Typ, {typeOf Exp Typ} -> {step Exp Exp'} -> {typeOf Exp' Typ}." in 
		 let preamble = Seq([Tactic(Induction(1)) ; Tactic(Intros(["Main" ; "Step"])) ; Tactic(Named("Hyp1", Case("Main")))]) in
		 let proofConstructors = List.map (subProofConstructor ldl) (ldl_getTermDeclForConstructors ldl) in 
		 let proofEliminators = List.map (subProofEliminator ldl subtyping) (List.concat (List.map specType_getEliminators (ldl_getTypes ldl))) in 
		 let proofDerived = List.map (subProofDerived ldl) (ldl_getDerived ldl) in 
		 let proofErrorHandlers = if ldl_containErrors ldl then List.map (subProofErrorHandler ldl subtyping) (specError_getHandlers (ldl_getError ldl)) else [] in 
		 let proofError = if ldl_containErrors ldl then [subProofConstructor ldl (specTerm_getSig (ldl_getErrorDeclaration ldl))] else [] in 
		 let proofSubsumptionCase = if is_none subtyping then [] else [Tactic(Apply("IH", ["Hyp1" ; "Step"])) ; Tactic(Search)] in 
		   error_types_all_lemma ldl subtyping 
		   @ List.concat (List.map listPreserveLemma (ldl_getLists_typeDecls ldl))
		   @ List.concat (List.map listPreserveLemmaUpdate (ldl_getListsThatUseUpdate_typeDecls ldl)) 
		   @ [Theorem(theorem, Seq(preamble::proofConstructors @ proofEliminators @ proofDerived @ proofErrorHandlers @ proofError @ proofSubsumptionCase))]
		