
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open ListManagement
open Proof
open Subtyping 
open GenerateLambdaProlog

let eachCanonicalForm nonResults errorSpec upTo typeSpec = 
	let typeOperator = type_getOperator (specType_getSig typeSpec) in 
	let (canonical, newVars) = type_getCanonical (specType_getSig typeSpec) in 
	let newVarsInString = List.map toString newVars in
	let constructorsSpecs = (specType_getConstructors typeSpec) in 
	let constructorsTermDecls = List.map specTerm_getSig constructorsSpecs in 
	let induction = if upTo then "induction on 1. \n" else "" in 
	let theorem = "Theorem " ^ " canonical_form_" ^ typeOperator ^ " : " ^ universalQuantification ("E"::newVarsInString) ^ "{typeOf E " ^ (toString canonical) ^ "} -> {value E} -> " ^ String.concat " \\/ " (List.map (term_existentiallyClosedEquation "E") constructorsTermDecls ) ^ ".\n" ^ induction in
	let preamble = createSeq([Intros(["Main" ; "Value"]) ; Named("Subsumption", Case("Main"))]) in
	let numberOfConstructors = List.length constructorsSpecs in 
	let numberOfConstructors = if typeDecl_isListButNotSelf (specType_getSig typeSpec) then numberOfConstructors + 1 else numberOfConstructors in 
	let searchForEachValueFormed = if typeDecl_isSelfList (specType_getSig typeSpec) then [Tactic(Search) ; Tactic(Search)] else [Tactic(Search)] in 
	let proofConstructors = Seq(repeat (Seq([Tactic(Case("Value"))] @ searchForEachValueFormed)) numberOfConstructors) in 
	let unifiableNonResults = List.length (List.filter (unifiableWithConstructor typeOperator) (specTerms_getAllTypingRules nonResults)) in
	let proofUnifiableNonResults = Seq(repeat (Tactic(Case("Value"))) unifiableNonResults) in 
	let proofErrors = if is_none errorSpec then Qed else 
		let unifiableErrors = 1 + List.length (List.filter (unifiableWithConstructor typeOperator) (specError_getHandlersTypingRules errorSpec)) in 
		Seq(repeat (Tactic(Case("Value"))) unifiableErrors) in 
 	let finalUpTo = 
		if upTo then 
			if typeDecl_isList (specType_getSig typeSpec) 
				then [Tactic(Named("Cases", Apply(inversion_subtype_NAME ^ "_" ^ typeOperator , ["Subsumption1"]))) ; Tactic(Case("Cases")) ; Tactic(Apply("IH", ["Subsumption" ; "Value"])) ; Tactic(Search) ; Tactic(Apply("IH", ["Subsumption" ; "Value"])) ; Tactic(Search)]
				else [Tactic(Apply(inversion_subtype_NAME ^ "_" ^ typeOperator , ["Subsumption1"])) ; Tactic(Apply("IH", ["Subsumption" ; "Value"])) ; Tactic(Search)]  
		else [] 
		 in Theorem(theorem, Seq([preamble ; proofConstructors ; proofUnifiableNonResults ; proofErrors] @ finalUpTo))

let generateCanonicalFormsLemma ldl subtyping = let upTo = is_some subtyping in 
	match ldl with SafeTypedLanguage(types, derived, errorSpec) -> 
		let typesThatHaveEliminators = List.filter (fun specType -> not (specType_getEliminators specType = [])) types in 
		List.map (eachCanonicalForm ((ldl_getAllEliminators ldl) @ derived) errorSpec upTo) typesThatHaveEliminators


