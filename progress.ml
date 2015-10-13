
open Batteries
open Aux
open Type_system
open Proof

let dynamicSemantics = "step"

let rec toString term = match term with 
  | Var(name) -> name
  | Constructor(name, arguments) -> name ^ " " ^ String.concat " " (List.map toString arguments)

let progressDefinition ts = if (ts_containErrors ts) then "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := {error E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."
	else "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."
let appealToCanonicalForm signatureTerms termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
    let typeBeingDestructed =  info_destructedType info in 
    let canonicalFormsDecl =  getConstructorsByOp typeBeingDestructed signatureTerms in 
		  [Tactic(Named("Canonical", Assert(String.concat " \\/ " (List.map (existentiallyClosedEquation "E1") canonicalFormsDecl)))) ; Tactic(Backchain("canonical_form", typeBeingDestructed)) ; Tactic(Case("Canonical")) ; RepeatPlain(List.length canonicalFormsDecl, Tactic(Search))]


let preambleproof_progress_lemmas isNonValue = if isNonValue then Seq([Tactic(Intros(["Main" ; "E1"])) ; Tactic(Case("Main")) ; Tactic(Named("ProgressClause", Case("E1")))]) else Seq([Tactic(Intros(["Main"])) ; Tactic(Case("Main"))])

let statement_progress_lemmas termDecl extraPremise = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	let (canonical, vars) = canonicalForTerm termDecl in 
	let c = termDelc_getOperator termDecl in 
	"Theorem progress_" ^ c ^ " : forall" ^ toStringFromList vars ^ " T, {typeOf (" ^ toString canonical ^ ") T} -> " ^ extraPremise ^ "progresses (" ^ toString canonical ^ ")." 

let progressLemmas signatureTerms termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	let extraPremise = if termDecl_containTerms termDecl then "progresses E1 -> " else "" in 
	let theorem = statement_progress_lemmas termDecl extraPremise in 
	let preamble = preambleproof_progress_lemmas true in 
	let possibleErrorCase = if getErrors signatureTerms = [] then [] else if List.mem termDecl (getErrorHandlers signatureTerms) then [Tactic(Case("ProgressClause")) ; Tactic(Search)] else [Tactic(Search)] in 
	let proofDestructingArgument = if (is_destructing info) then (appealToCanonicalForm signatureTerms termDecl) else [Tactic(Search)] in 
	let proof = Seq( proofDestructingArgument @ possibleErrorCase @ [Tactic(Search)]) in
		if termDecl_containTerms termDecl then Theorem(theorem, Seq([preamble ; proof])) else Theorem(theorem, Tactic(Search))


(* returns progressDef, (theorem, proof) list *)
let generateProgressLemmas ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> 
		(List.map (progressLemmas signatureTerms) (getNonResults signatureTerms)) 

		  (* 
    let canonicalForms =  List.map canonicalForTermNoClash canonicalFormsDecl in			
	let transformation = fun entry -> match entry with (canonical, vars) -> if vars = [] then "E1 = " ^ (toString canonical) else "exists " ^ toStringFromList vars ^ ", E1 = " ^ (toString canonical) in
	let transformation = fun entry -> match entry with (canonical, vars) -> if vars = [] then "E1 = " ^ (toString canonical) else "exists " ^ toStringFromList vars ^ ", E1 = " ^ (toString canonical) in
		  [Tactic(Named("Canonical", Assert(String.concat " \\/ " (List.map transformation canonicalForms)))) ; Tactic(Backchain("canonical_form", typeBeingDestructed)) ; Tactic(Case("Canonical")) ; RepeatPlain(List.length canonicalForms, Tactic(Search))]
			  
			  @ (List.map (progressLemmas signatureTerms) (getDerivedDestructors signatureTerms))

		  	Alrogithm for progress lemma for constructors: search.
		  	Alrogithm for progress lemma for destructors: case E1, appeal to canonical form, and for all canonical forms do search. then do search for the progress case (when E1 progresses)
		  *)

let generateProgressTheorem ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let theorem = "Theorem progress : forall E T, {typeOf E T} -> progresses E. \ninduction on 1. intros Main. E1 : case Main." in
         let proofBycases = (fun termDecl -> if termDecl_containTerms termDecl then Seq([Tactic(Apply("IH", ["E1"])) ; Tactic(Backchain("progress", termDelc_getOperator termDecl))]) else Tactic(Backchain("progress", termDelc_getOperator termDecl))) in
		 let proofConstructors = Seq(repeat (Tactic(Search)) (List.length (getConstructors signatureTerms))) in 
         let proofNonResults = Seq(List.map proofBycases (getNonResults signatureTerms)) in
		 let proofErrors = Seq(repeat (Tactic(Search)) (List.length (getErrors signatureTerms))) in 
          Theorem(theorem, Seq([proofConstructors ; proofNonResults ; proofErrors]))

		  (*
			  
		 let proofDerivedNoDestructors = Seq(repeat (Tactic(Search)) (List.length (getDerivedNoDestructors signatureTerms))) in 
		 let proofDerivedDestructors = Seq(List.map proofBycases (getDerivedDestructors signatureTerms)) in
		 let proofErrorHandlers = Seq(List.map proofBycases (getErrorHandlers signatureTerms)) in in 
		 let proofErrors = Seq(repeat (Tactic(Search)) (List.length (getErrors signatureTerms))) in 
          Theorem(theorem, Seq([proofConstructors ; proofDestructors ; proofDerivedNoDestructors ; proofDerivedDestructors ; proofErrorHandlers ; proofErrors]))
			  
		  	Alrogithm for main progress:
			  for all constructors: search.
			  for all destructors, assume the first n arguments are of kind term, then apply the inductive hypothesis on those arguments and then backchain with the progress lemma.
		  *)