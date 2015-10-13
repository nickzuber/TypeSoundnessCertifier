
open Type_system
open Aux
open Proof

let eachCanonicalForm signatureTerms typeDecl = match typeDecl with DeclType(c,arguments) ->
         let constructorsOfc = (getConstructorsByOp c signatureTerms) in   
         let (canonical, newVars) = canonicalForType typeDecl in 
		 let newVarsInString = List.map toString newVars in
         let theorem = "Theorem " ^ " canonical_form_" ^ c ^ " : " ^ universalQuantification ("E"::newVarsInString) ^ "{typeOf E " ^ (toString canonical) ^ "} -> {value E} -> " ^ String.concat " \\/ " (List.map (existentiallyClosedEquation "E") constructorsOfc ) ^ "." in
         let preamble = createSeq([Intros(["Main" ; "Value"]) ; Case("Main")]) in
		 let proofConstructorsOfc = Seq(repeat (Tactic(Search)) (List.length constructorsOfc)) in 
		 let proofNonResults = Seq(repeat (Tactic(Case("Value"))) (List.length (getNonResults signatureTerms))) in 
		 let proofErrors = Seq(repeat (Tactic(Case("Value"))) (List.length (getErrors signatureTerms))) in 
          Theorem(theorem, Seq([preamble ; proofConstructorsOfc ; proofNonResults ; proofErrors]))

			       (* this function below returns a list of Theorem(theorem,proof) *)
let generateCanonicalFormsLemma ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
          (List.map (eachCanonicalForm signatureTerms) signatureTypes)


(*
		  Algorithm:
		  	for all types T, generate the canonical form theorem for T. that is for all e of type T and value e, the it is the OR of the constructor. 
		  	Proof: 	for all constructors of T: search.
		  		   	for all deconstructors, "case Value." for contradiction. 
*) 
		  
(* 
         let proof = Seq([RepeatPlain(List.length constructorsOfc, Tactic(Search))]) in
         let dismissedCases = Seq([RepeatPlain(numberOfNonResults, Tactic(Case("Value")))]) in 
		  
		  needed. getConstructors getDestructors only *)		  