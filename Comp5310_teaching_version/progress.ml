open Topo
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open ListManagement
open ListLemmas
open Proof
open CanonicalForms
open GenerateLambdaProlog

let dynamicSemantics = "step"
let toE i = "E" ^ (string_of_int i)
let toPrgsE i = "PrgsE" ^ (string_of_int i)
let toTypeOfE i = "TypeOfE" ^ (string_of_int i)
let progressImplication var = "progresses " ^ var ^ " -> "
let toCaseWithProgressClause i = if i = 1 then Tactic(Named("ProgressClause", Case((toPrgsE i)))) else toCase (toPrgsE i)

let turnToProgresses = (formula_turnToUnaryPredicate "progresses")

let combinatoricsOfSearches sensitivePositions errorSpec flagErrorHandler = 
	let multiply = if is_none errorSpec then 1 else 2 in 
	let subTreeToDischarge = if flagErrorHandler then (List.length sensitivePositions) - 1 else (List.length sensitivePositions) in 
		repeat (Tactic(Search)) (subTreeToDischarge * multiply)

let progressDefinition ldl = 
	if (ldl_containErrors ldl) 
	then "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := {error E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."
	else "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."

let appealToCanonicalForm typeSpec updateVar = 
	let isList = typeDecl_isList (specType_getSig typeSpec) in 
	let constructors = (specType_getConstructors typeSpec) in 
	let numberOfConstructors = List.length constructors in 
	let typeBeingProved = (specType_getTypeName typeSpec) in 
	let caseCanonicalIfNecessary = if numberOfConstructors = 1 || isList then Qed else Tactic(Case("Canonical")) in  
	let applyUpdateSynch = if is_some updateVar then [Tactic(Apply(updateSynchLemma (chop_last_char typeBeingProved 'T'), ["MemberSynch with E2 = " ^ generateTerm (get updateVar)]))] else [] in 
	let callLemmaForListsIfNecessary = if isList then [Tactic(Named("MemberSynch", Apply(memberSynchLemma typeBeingProved, [(toTypeOfE 1) ; (toTypeOfE 2)])))] @ applyUpdateSynch else [Qed] in 
  [Tactic(Named("Canonical", Apply("canonical_form_" ^ typeBeingProved, [(toTypeOfE 1) ; "ProgressClause"]))) ; caseCanonicalIfNecessary] @ callLemmaForListsIfNecessary @ [RepeatPlain(numberOfConstructors, Tactic(Search))] 

let preambleproof_progress_lemmas sensitivePositionsRaw positionsInOrderRaw = 
	let sensitivePositions = List.map toPrgsE sensitivePositionsRaw in 
	if sensitivePositions = [] then Qed else Seq([Tactic(Intros("Main" :: sensitivePositions)) ; Tactic(Named((toTypeOfE 1), Case("Main")))] @ List.map toCaseWithProgressClause positionsInOrderRaw)

let statement_progress_lemmas termDecl sensitivePositions = 
	let extraPremise = String.concat "" (List.map progressImplication (List.map toE sensitivePositions)) in 
	let (canonical, vars) = term_getCanonical termDecl in 
	"Theorem progress_" ^ (term_getOperator termDecl) ^ " : forall" ^ toStringFromList vars ^ " T, {typeOf (" ^ toString canonical ^ ") T} -> " ^ extraPremise ^ "progresses (" ^ toString canonical ^ ").\n" 

	

let progressLemmasList upTo specTerm = 
	let termDecl = specTerm_getSig specTerm in 
	let c = specTerm_getOperator specTerm in 
	if termDecl_isSelfList termDecl  
		then 
			(let typingPremise = Formula(typeOfWithSelf, [Constructor(c ^ "T", [Var "Whole"]) ; Constructor(c, [Var "List"])], [Var "T"]) in 
			let progressConclusion  = turnToProgresses (Formula(typing, [Constructor(c, [Var "List"])], [Var "T"])) in  
			let theorem = "Theorem progress_" ^ c ^ " : forall Whole List T, " ^ wrappedInBrackets (generateFormula typingPremise)  ^ " -> " ^ (generateFormula progressConclusion) ^ ".\n" in 
			let proof = Seq([Tactic(Intros(["TypeOf"])) ; Tactic(Case("TypeOf")) ; Tactic(Search) ; Tactic(Search)]) in 
			  [Theorem(theorem, proof)])
		else 
	let sensitivePositions = List.hd (term_getContextualPositions termDecl) in 
	let typingRuleEmpty = specTerm_getTyping specTerm in 
	let typingRuleCons = List.hd (specTerm_getReduction specTerm) in (* remember, you have placed that typing rule as first of reductions *)
	let progress_premises_empty = turnToProgresses (rule_getConclusion typingRuleEmpty) in  
	let progress_premises_cons = List.map turnToProgresses (List.filter (fun premise -> not (formula_isWithContext premise)) (List.filter formula_isTyping (rule_getPremises typingRuleCons) @ [rule_getConclusion typingRuleCons])) in  
	let progressFact_empty = formula_freeOutput (rule_getConclusion typingRuleEmpty) in 
	let progressFact_cons = formula_freeOutput (rule_getConclusion typingRuleCons) in 
	let vars_empty = formula_getAllVariables progressFact_empty in 
	let vars_cons = formula_getAllVariables progressFact_cons in 
	let statement_empty = "Theorem progress_" ^ c ^ "_empty : forall" ^ toStringFromList vars_empty ^ ", " ^ wrappedInBrackets (generateFormula progressFact_empty) ^ " -> " ^ (generateFormula progress_premises_empty) ^ "." in 
	let statement_cons = "Theorem progress_" ^ c ^ "_cons : forall" ^ toStringFromList vars_cons ^ ", " ^ wrappedInBrackets (generateFormula progressFact_cons) ^ " -> " ^ (String.concat " -> " (List.map generateFormula progress_premises_cons)) ^ "." in
    let induction = if upTo then [Tactic(Induction(1))] else [] in 
	let progressAssumptions i rule = toPrgsE (i+1) in 
	(* below it is (List.tl progress_premises_cons) because progress_premises_cons also contains the conclusion *)
	let subsumption = if upTo then [Tactic(Apply("IH", "TypeOfE1" :: List.mapi progressAssumptions (List.tl progress_premises_cons))) ; Tactic(Search)] else [] in 
	  [
	 Theorem(statement_empty, Tactic(Search)) ; 
	 Theorem(statement_cons, 
		 Seq(induction @ 
			 [Tactic(Intros("Main" :: List.mapi progressAssumptions (List.tl progress_premises_cons))) ; Tactic(Named((toTypeOfE 1), Case("Main"))) ; 
		      Tactic(Named("ProgressClause", Case((toPrgsE 1))))]
			  @ (if sensitivePositions = 3 then [] else [Tactic(Named("ListMayStep", Case((toPrgsE 2))))])
			  @ [Tactic(Search)]
			  @ (if sensitivePositions = 3 then [] else [Tactic(Case("ListMayStep")) ; Tactic(Search) ; Tactic(Search)])
			  @ [Tactic(Search)] 
			  @ subsumption
	 	)) 
	 	] 
	
let progressLemmasByOperators errorSpec typeSpec flagErrorHandler upTo eliminator =  
	let termDecl = specTerm_getSig eliminator in 
	if termDecl_isList termDecl then progressLemmasList upTo eliminator else 
	let sensitivePositions = (term_getContextualPositions termDecl) in 
	let positionsInOrder = topo_compute_order (term_getContextInfo termDecl) in 
	let induction = if upTo && not (sensitivePositions = []) then "induction on 1. \n" else "" in
	let theorem  = (statement_progress_lemmas termDecl sensitivePositions) ^ induction in 	
	let preamble = preambleproof_progress_lemmas sensitivePositions positionsInOrder in 
	let proof_leftmost = if is_none typeSpec then [Tactic(Search)] else appealToCanonicalForm (get typeSpec) (rule_doesItUseUpdate eliminator (get typeSpec)) in 
	let proofDischargeAllSubtrees = combinatoricsOfSearches sensitivePositions errorSpec flagErrorHandler in 
	let finishErrorHandlerIfNeeded = if flagErrorHandler then [Tactic(Case("ProgressClause")) ; Tactic(Search) ; Tactic(Search)] else [] in 
 	let finalUpTo = if upTo && not (sensitivePositions = []) then [Tactic(Apply("IH", ["TypeOfE1"] @ List.map toPrgsE sensitivePositions)) ; Tactic(Search)]  else [] in 
	let proof = proof_leftmost @ proofDischargeAllSubtrees @ finishErrorHandlerIfNeeded @ finalUpTo
		in [Theorem(theorem, Seq([preamble ; Seq(proof)]))] 

let progressLemmasTypes errorSpec upTo typeSpec = 
	List.concat (List.map (progressLemmasByOperators errorSpec None false upTo) (specType_getConstructors typeSpec))
		@
	List.concat (List.map (progressLemmasByOperators errorSpec (Some typeSpec) false upTo) (specType_getEliminators typeSpec))


(* returns progressDef, (theorem, proof) list *)
let generateProgressLemmas ldl subtyping = 
	let upTo = is_some subtyping in 
	match ldl with SafeTypedLanguage(types, derived, errorSpec) -> 
		let progressLemmasForErrorRelated = if is_none errorSpec then [] else List.concat (List.map (progressLemmasByOperators errorSpec None true upTo) (specError_getHandlers errorSpec)) @ (progressLemmasByOperators errorSpec None false upTo) (specError_getError errorSpec) in 
   	 	List.concat (List.map listSynchLemma (ldl_getLists_typeDecls ldl))
		@ List.concat (List.map (progressLemmasTypes errorSpec upTo) types) @ List.concat (List.map (progressLemmasByOperators errorSpec None false upTo) derived) @ progressLemmasForErrorRelated

let callProgressLemma operator = 
	let termDecl = specTerm_getSig operator in 
	let op = term_getOperator termDecl in 
	let ctxPositions = adjustContextsIfList termDecl (term_getContextualPositions termDecl) in 
	let ctxPositions = if termDecl_isListButNotSelf termDecl then removeDuplicates (ctxPositions @ [2]) else ctxPositions in 
	let proofForEmptyIfNeeded = if termDecl_isListButNotSelf termDecl then [Tactic(Backchain("progress", op ^ "_empty"))] else [] in 
	let newOp = if termDecl_isListButNotSelf termDecl then op ^ "_cons" else op in 
		Seq(proofForEmptyIfNeeded @ [ForEach(List.map toTypeOfE ctxPositions, Tactic(Apply("IH", ["x"]))) ; Tactic(Backchain("progress", newOp))])

let generateProgressTheorem ldl subtyping = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> 
		 let upTo = is_some subtyping in 
         let theorem = "Theorem progress : forall E T, {typeOf E T} -> progresses E. \ninduction on 1. intros Main. TypeOfE1 : case Main." in
		 let proofConstructors = Seq(List.map callProgressLemma (List.concat (List.map specType_getConstructors types))) in 
		 let proofEliminators = Seq(List.map callProgressLemma (List.concat (List.map specType_getEliminators types))) in 
         let proofDerived = Seq(List.map callProgressLemma derived) in
		 let proofErrors = if is_none errorSpec then Qed else Seq(List.map callProgressLemma ((specError_getHandlers errorSpec) @ [specError_getError errorSpec])) in 
  		 let finalUpTo = if upTo then [Tactic(Apply("IH", ["TypeOfE1"])) ; Tactic(Search)]  else [] in 
          Theorem(theorem, Seq([proofConstructors ; proofEliminators ; proofDerived ; proofErrors] @ finalUpTo))

