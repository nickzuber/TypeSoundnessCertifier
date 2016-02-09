
open Batteries
open Option
open TypedLanguage
open SafeTypedLanguage
open Aux
open Proof

let eachCanonicalForm nonResults errorSpec typeSpec = 
	let typeOperator = type_getOperator (specType_getSig typeSpec) in 
	let (canonical, newVars) = type_getCanonical (specType_getSig typeSpec) in 
	let newVarsInString = List.map toString newVars in
	let theorem = "Theorem " ^ " canonical_form_" ^ typeOperator ^ " : " ^ universalQuantification ("E"::newVarsInString) ^ "{typeOf E " ^ (toString canonical) ^ "} -> {value E} -> " ^ String.concat " \\/ " (List.map (existentiallyClosedEquation "E") (specType_getConstructors typeSpec) ) ^ "." in
	let preamble = createSeq([Intros(["Main" ; "Value"]) ; Case("Main")]) in
	let proofConstructors = Seq(repeat (Tactic(Search)) (List.length (specType_getConstructors typeSpec))) in 
	let unifiableNonResults = List.length (List.filter (unifiableWithConstructor typeOperator) (specTerms_getAllTypingRules nonResults)) in
	let proofUnifiableNonResults = Seq(repeat (Tactic(Case("Value"))) unifiableNonResults) in 
	let proofErrors = if is_none errorSpec then Qed else 
		let unifiableErrors = 1 + List.length (List.filter (unifiableWithConstructor typeOperator) (specError_getHandlersTypingRules errorSpec)) in 
		Seq(repeat (Tactic(Case("Value"))) unifiableErrors)  
          in Theorem(theorem, Seq([preamble ; proofConstructors ; proofUnifiableNonResults ; proofErrors]))

let generateCanonicalFormsLemma tl = 
	match tl with SafeTypedLanguage(types, others, errorSpec) -> 
		List.map (eachCanonicalForm ((sl_getAllEliminators tl) @ others) errorSpec) types


(*
		
		1 + .. because the error has always type T and unifies. 
	let proofEliminators = Seq(repeat (Tactic(Case("Value"))) (List.length eliminators)) in 
		
		-> match signature with DeclType(c,arguments) ->
		  Algorithm:
		  	for all types T, generate the canonical form theorem for T. that is for all e of type T and value e, the it is the OR of the constructor. 
		  	Proof: 	for all constructors of T: search.
		  		   	for all deconstructors whose typing rule conclusion UNIFY with T, "case Value." for contradiction. 
		  			Interestingly: this is the only point where a complex type in the conclusion change the methodology. 
*) 
		  
