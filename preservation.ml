
open Batteries
open Option
open Aux
open Type_system
open Proof

let hypothetical argumentEntry = match argumentEntry with 
	| Abstraction("term", _) -> true 
	| otherwise -> false 

let substitutionLemmaForAbstractions nestingLevel rule index argumentEntry = match argumentEntry with 
| Abstraction(typ1, typ2) -> 
	let provedTerm = rule_getInputTerm rule in 
	let targetTerm = rule_getOutputTerm rule in 
	let Constructor(c,arguments) = if nestingLevel = 1 then provedTerm else term_getFirstArgument provedTerm in 
	let abstractedVar = try List.nth arguments index with Invalid_argument arg -> raise (Failure "here") in 
		(match retrieveApplication abstractedVar targetTerm with 
			| None -> Qed
			| Some Var(appliedVar) -> 
				let appliedVarIndex = retrievePosition (Var(appliedVar)) provedTerm in 
				let abstractedVarIndex = retrievePosition abstractedVar provedTerm in 
				let argHyp = "Arg" ^ abstractedVarIndex in (* (string_of_int nestingLevel) ^  *)
				let cutHyp = "Arg" ^ appliedVarIndex in
				if hypothetical argumentEntry then Tactic(InstAndCut(argHyp, appliedVar, cutHyp)) else Tactic(Inst(argHyp, appliedVar)))	
| otherwise -> Qed

let singleDestruction = Tactic(Named("Arg1_1", CaseKeep("TypeOf")))
let doubleDestruction = Seq([Tactic(Named("Arg1_1", CaseKeep("TypeOf"))) ; Tactic(Named("Arg2_1", CaseKeep("Arg1_1")))])

let subProofForASingleDestruction nestingLevel termDecl currentStepRule = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	Seq(List.mapi (substitutionLemmaForAbstractions nestingLevel currentStepRule) arguments) 

let subProofReductionPerCanonical termDecl canonicalDecl rule = if is_none rule then raise (Failure ("ERROR:: The destructor" ^ termDelc_getOperator termDecl ^ " does not destruct all the constructors. Progress fails.")) 
	else let currentStepRule = get rule in 
	Seq([doubleDestruction ; subProofForASingleDestruction 1 termDecl currentStepRule ; subProofForASingleDestruction 2 canonicalDecl currentStepRule ; Tactic(Search)])
	
let subProofDestructors signatureTerms rules termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	let canonicalDecls = (getConstructorsByOp (info_destructedType info) signatureTerms) in 
	Seq(List.map2 (subProofReductionPerCanonical termDecl) canonicalDecls (List.map (rule_seekStepOfWith c rules) canonicalDecls)) 

let subProofDerivedNoDestructors signatureTerms rules termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) ->
	Seq([singleDestruction ; subProofForASingleDestruction 1 termDecl (rule_seekStepOf c rules) ; Tactic(Search)])

let subProofDerivedDestructors signatureTerms rules termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	Seq([singleDestruction ; subProofForASingleDestruction 1 termDecl (rule_seekStepOf c rules) ; Tactic(Search)])

let subProofErrorHandlers signatureTerms rules termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	let errorDecl = (List.hd (getErrors signatureTerms)) in let currentStepRule = rule_seekStepOfWith c rules errorDecl in 
	if is_none currentStepRule then raise (Failure "ERROR:: ErrorHandlers does not have a rule for handlin the error")
	else (Seq([singleDestruction ; Tactic(Search) ; (subProofReductionPerCanonical termDecl errorDecl currentStepRule) ]))

let subProofContextual termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	let single_line = fun index -> let hypByArgIndex = "TypeOf" ^ (string_of_int index) in Seq([Tactic(Named("TypeOf1", Case("TypeOf"))) ; Tactic(Apply("IH", ["Step" ; hypByArgIndex])) ; Tactic(Search)]) in 
	 List.map single_line (context_getFlattenedInfo ctx)		 

let generatePreservationTheorem sl = 
         let theorem = "Theorem preservation : forall E E' T, {step E E'} -> {typeOf E T} -> {typeOf E' T}." in 
		 let preamble = Seq([Tactic(Induction(1)) ; Tactic(Intros(["Main" ; "TypeOf"])) ; Tactic(Named("Step", Case("Main")))]) in
         let proofReductionsDestructors = List.map (subProofEliminators sl) (List.concat (List.map specType_getEliminators types)) in 
		 let proofReductionsOthers = List.map (subProofDerivedNoDestructors signatureTerms rules) (getDerivedNoDestructors signatureTerms) in 
		 let proofErrorHandlers = (List.map (subProofErrorHandlers signatureTerms rules) (getErrorHandlers signatureTerms)) in 
         let proofContextual = List.concat (List.map subProofContextual (getContextualTerms signatureTerms)) in
		 let proofErrorContexts = if (sl_containErrors sl) then List.map (fun tactic -> Seq([Tactic(Case("Step")) ; Tactic(Named("TypeOf1", Case("TypeOf"))) ; tactic ; Tactic(Search)])) (List.map (toCaseTactic "TypeOf") (errorPropagatingContexts signatureTerms)) else [] in 
            Theorem(theorem, Seq( (preamble::proofReductionsDestructors) @ proofReductionsDerivedNoDestructors @ proofReductionsDerivedDestructors @ proofErrorHandlers @ proofContextual @ proofErrorContexts))
			
			
			(* (seekDeclTermOf signatureTerms canonical_c)
				Algorithm for reduction rules:
				case on destructive argument, create a substitution lemma for the other arguments if hypothetical. If no destruction of a type, then the proof is done with search. 
				  if instead, the operator destruct a type, then we case again on the first argument which is the nested operator. Now, create a substitution lemma for ALL the arguments if hypothetical (including the first of the nested). Conclude with search. 				
			*)