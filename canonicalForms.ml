
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open Proof
open GenerateLambdaProlog

let universalQuantification vars = if vars = [] then "" else "forall " ^ String.concat " " vars ^ ", "

let existentiallyClosedEquation var termSpec = 
	let (canonical, vars) = term_getCanonicalNoClash (specTerm_getSig termSpec) in 
	if vars = [] then var ^ " = " ^ (toString canonical) else let existentials = "exists " ^ String.concat " " (List.map toString vars) ^ ", " in 
	let valueTests = String.concat "" (List.map addAnd (List.map wrappedInBrackets (List.map generateFormula (List.map toValuePremise  (List.map (nthMinusOne vars) (term_getValPositions (specTerm_getSig termSpec))))))) in 
	 "(" ^ existentials ^ var ^ " = " ^ (toString canonical) ^ valueTests ^ ")"

let eachCanonicalForm nonResults errorSpec typeSpec = 
	let typeOperator = type_getOperator (specType_getSig typeSpec) in 
	let (canonical, newVars) = type_getCanonical (specType_getSig typeSpec) in 
	let newVarsInString = List.map toString newVars in
	let theorem = "Theorem " ^ " canonical_form_" ^ typeOperator ^ " : " ^ universalQuantification ("E"::newVarsInString) ^ "{typeOf E " ^ (toString canonical) ^ "} -> {value E} -> " ^ String.concat " \\/ " (List.map (existentiallyClosedEquation "E") (specType_getConstructors typeSpec) ) ^ "." in
	let preamble = createSeq([Intros(["Main" ; "Value"]) ; Case("Main")]) in
	let proofConstructors = Seq(repeat (Seq([Tactic(Case("Value")) ; Tactic(Search)])) (List.length (specType_getConstructors typeSpec))) in 
	let unifiableNonResults = List.length (List.filter (unifiableWithConstructor typeOperator) (specTerms_getAllTypingRules nonResults)) in
	let proofUnifiableNonResults = Seq(repeat (Tactic(Case("Value"))) unifiableNonResults) in 
	let proofErrors = if is_none errorSpec then Qed else 
		let unifiableErrors = 1 + List.length (List.filter (unifiableWithConstructor typeOperator) (specError_getHandlersTypingRules errorSpec)) in 
		Seq(repeat (Tactic(Case("Value"))) unifiableErrors)  
          in Theorem(theorem, Seq([preamble ; proofConstructors ; proofUnifiableNonResults ; proofErrors]))

let generateCanonicalFormsLemma tl = 
	match tl with SafeTypedLanguage(types, derived, errorSpec) -> 
		List.map (eachCanonicalForm ((ldl_getAllEliminators tl) @ derived) errorSpec) types


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
		  
