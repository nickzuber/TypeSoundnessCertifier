open Topo
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open Proof
open CanonicalForms

let dynamicSemantics = "step"
let toE i = "E" ^ (string_of_int i)
let toPrgsE i = "PrgsE" ^ (string_of_int i)
let toTypeOfE i = "TypeOfE" ^ (string_of_int i)
let progressImplication var = "progresses " ^ var ^ " -> "
let toCaseWithProgressClause i = if i = 1 then Tactic(Named("ProgressClause", Case((toPrgsE i)))) else toCase (toPrgsE i)

let combinatoricsOfSearches sensitivePositions errorSpec flagErrorHandler = 
	let multiply = if is_none errorSpec then 1 else 2 in 
	let subTreeToDischarge = if flagErrorHandler then (List.length sensitivePositions) - 1 else (List.length sensitivePositions) in 
		repeat (Tactic(Search)) (subTreeToDischarge * multiply)

let progressDefinition ldl = 
	if (ldl_containErrors ldl) 
	then "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := {error E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."
	else "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."

let appealToCanonicalForm typeSpec = 
	let constructors = (specType_getConstructors typeSpec) in 
	let typeBeingProved = (specType_getTypeName typeSpec) in 
	let caseCanonicalIfNecessary = if List.length constructors = 1 then Qed else Tactic(Case("Canonical")) in 
  [Tactic(Named("Canonical", Apply("canonical_form_" ^ typeBeingProved, [(toTypeOfE 1) ; "ProgressClause"]))) ; caseCanonicalIfNecessary ; RepeatPlain((List.length constructors), Tactic(Search))] 

let preambleproof_progress_lemmas sensitivePositionsRaw positionsInOrderRaw = 
	let sensitivePositions = List.map toPrgsE sensitivePositionsRaw in 
	if sensitivePositions = [] then Qed else Seq([Tactic(Intros("Main" :: sensitivePositions)) ; Tactic(Named((toTypeOfE 1), Case("Main")))] @ List.map toCaseWithProgressClause positionsInOrderRaw)

let statement_progress_lemmas termDecl sensitivePositions = 
	let extraPremise = String.concat "" (List.map progressImplication (List.map toE sensitivePositions)) in 
	let (canonical, vars) = term_getCanonical termDecl in 
	"Theorem progress_" ^ (term_getOperator termDecl) ^ " : forall" ^ toStringFromList vars ^ " T, {typeOf (" ^ toString canonical ^ ") T} -> " ^ extraPremise ^ "progresses (" ^ toString canonical ^ ")." 

let progressLemmasByOperators errorSpec typeSpec flagErrorHandler eliminator =  
	let termDecl = specTerm_getSig eliminator in 
	let sensitivePositions = (term_getContextualPositions termDecl) in 
	let positionsInOrder = topo_compute_order (term_getContextInfo termDecl) in 
	let theorem  = statement_progress_lemmas termDecl sensitivePositions in 	
	let preamble = preambleproof_progress_lemmas sensitivePositions positionsInOrder in 
	let proof_leftmost = if is_none typeSpec then [Tactic(Search)] else appealToCanonicalForm (get typeSpec) in 
	let proofDischargeAllSubtrees = combinatoricsOfSearches sensitivePositions errorSpec flagErrorHandler in 
	let finishErrorHandlerIfNeeded = if flagErrorHandler then [Tactic(Case("ProgressClause")) ; Tactic(Search) ; Tactic(Search)] else [] in 
	let proof = proof_leftmost @ proofDischargeAllSubtrees @ finishErrorHandlerIfNeeded
		in Theorem(theorem, Seq([preamble ; Seq(proof)])) 

let progressLemmasTypes errorSpec typeSpec = 
	List.map (progressLemmasByOperators errorSpec None false) (specType_getConstructors typeSpec)
		@
	List.map (progressLemmasByOperators errorSpec (Some typeSpec) false) (specType_getEliminators typeSpec)

(* returns progressDef, (theorem, proof) list *)

let generateProgressLemmas ldl = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> 
	let progressLemmasForErrorRelated = if is_none errorSpec then [] else List.map (progressLemmasByOperators errorSpec None true) (specError_getHandlers errorSpec) @ [(progressLemmasByOperators errorSpec None false) (specError_getError errorSpec)] in 
 	   List.concat (List.map (progressLemmasTypes errorSpec) types) @ List.map (progressLemmasByOperators errorSpec None false) derived @ progressLemmasForErrorRelated

let callProgressLemma operator = let termDecl = specTerm_getSig operator in Seq([ForEach(List.map toTypeOfE (term_getContextualPositions termDecl), Tactic(Apply("IH", ["x"]))) ; Tactic(Backchain("progress", term_getOperator termDecl))])

let generateProgressTheorem ldl = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> 
         let theorem = "Theorem progress : forall E T, {typeOf E T} -> progresses E. \ninduction on 1. intros Main. TypeOfE1 : case Main." in
		 let proofConstructors = Seq(List.map callProgressLemma (List.concat (List.map specType_getConstructors types))) in 
		 let proofEliminators = Seq(List.map callProgressLemma (List.concat (List.map specType_getEliminators types))) in 
         let proofDerived = Seq(List.map callProgressLemma derived) in
		 let proofErrors = if is_none errorSpec then Qed else Seq(List.map callProgressLemma ((specError_getHandlers errorSpec) @ [specError_getError errorSpec])) in 
          Theorem(theorem, Seq([proofConstructors ; proofEliminators ; proofDerived ; proofErrors]))

