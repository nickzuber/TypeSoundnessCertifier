
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
let appealToCanonicalForm signatureTerms termDecl valuePositions = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
    let typeBeingDestructed =  info_destructedType info in 
    let canonicalFormsDecl =  getConstructorsByOp typeBeingDestructed signatureTerms in 
	let closeWithSearches = if getErrors signatureTerms = [] then repeat (Tactic(Search)) (List.length (List.drop 1 valuePositions)) else repeat (Tactic(Search)) ((List.length (List.drop 1 valuePositions)) * 2) in 
		  [Tactic(Named("Canonical", Assert(String.concat " \\/ " (List.map (existentiallyClosedEquation "E1") canonicalFormsDecl)))) ; Tactic(Backchain("canonical_form", typeBeingDestructed)) ; Tactic(Case("Canonical")) ; RepeatPlain(List.length canonicalFormsDecl, Tactic(Search))] @ closeWithSearches


let preambleproof_progress_lemmas isNonValue valuePositions = if isNonValue then Seq([Tactic(Intros("Main" :: valuePositions)) ; Tactic(Case("Main")) ; Tactic(Named("ProgressClause", Case("E1")))] @ (List.map toCase (List.drop 1 valuePositions))) else Seq([Tactic(Intros(["Main"])) ; Tactic(Case("Main"))])
let toE i = "E" ^ (string_of_int i)
let progressImplication var = "progresses " ^ var ^ " -> "

let statement_progress_lemmas termDecl valuePositions = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	let extraPremise = String.concat "" (List.map progressImplication valuePositions) in 
	let (canonical, vars) = canonicalForTerm termDecl in 
	let c = termDelc_getOperator termDecl in 
	"Theorem progress_" ^ c ^ " : forall" ^ toStringFromList vars ^ " T, {typeOf (" ^ toString canonical ^ ") T} -> " ^ extraPremise ^ "progresses (" ^ toString canonical ^ ")." 

let progressLemmas signatureTerms termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	let valuePositions = List.map toE (context_getFlattenedInfo ctx) in (* it should be (getArgumentsCheckedForValuehood c rules) *)
	let theorem = statement_progress_lemmas termDecl valuePositions in 
	let preamble = preambleproof_progress_lemmas true valuePositions in 
	let possibleErrorCase = if getErrors signatureTerms = [] then [] else if List.mem termDecl (getErrorHandlers signatureTerms) then [Tactic(Case("ProgressClause")) ; Tactic(Search)] else [Tactic(Search)] in 
	let proofDestructingArgument = if (is_destructing info) then (appealToCanonicalForm signatureTerms termDecl valuePositions) else [Tactic(Search)] in 
	let proof = Seq( proofDestructingArgument @ possibleErrorCase @ [Tactic(Search)]) in
		if termDecl_containTerms termDecl then Theorem(theorem, Seq([preamble ; proof])) else Theorem(theorem, Tactic(Search))

let progressLemmasValues isThereError termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
	let valuePositions = List.map toE (context_getFlattenedInfo ctx) in 
	let theorem = statement_progress_lemmas termDecl valuePositions in 
	let preamble = preambleproof_progress_lemmas true valuePositions in 
	let numberOfValuePremises = List.length (context_getFlattenedInfo ctx) in 
	let mult = if isThereError then 3 else 2 in 
	let proof = Seq(repeat (Tactic(Search)) (numberOfValuePremises * mult)) in
		Theorem(theorem, Seq([preamble ; proof])) 

(* returns progressDef, (theorem, proof) list *)
let generateProgressLemmas ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> 
	(List.map (progressLemmasValues (not (getErrors signatureTerms = []))) (getValuesWithValues signatureTerms)) @ (List.map (progressLemmas signatureTerms) (getNonResults signatureTerms)) 

		  (* 
		  	Alrogithm for progress lemma for constructors: search.
		  	Alrogithm for progress lemma for destructors: case E1, appeal to canonical form, and for all canonical forms do search. then do search for the progress case (when E1 progresses)
		  *)

let generateProgressTheorem ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let theorem = "Theorem progress : forall E T, {typeOf E T} -> progresses E. \ninduction on 1. intros Main. E1 : case Main." in
         let proofBycases = (fun termDecl -> let valuePositions = List.map toE (termDelc_getCtxInfo termDecl) in if termDecl_containTerms termDecl then Seq([ForEach(valuePositions, Tactic(Apply("IH", ["x"]))) ; Tactic(Backchain("progress", termDelc_getOperator termDecl))]) else Tactic(Backchain("progress", termDelc_getOperator termDecl))) in
		 let proofConstructors = Seq(repeat (Tactic(Search)) (List.length (getConstructors signatureTerms) - List.length (getValuesWithValues signatureTerms))) in 
         let proofNonResults = Seq(List.map proofBycases ((getValuesWithValues signatureTerms) @ (getNonResults signatureTerms))) in
		 let proofErrors = Seq(repeat (Tactic(Search)) (List.length (getErrors signatureTerms))) in 
          Theorem(theorem, Seq([proofConstructors ; proofNonResults ; proofErrors]))

		  (*			  
		  	Alrogithm for main progress:
			  for all constructors: search.
			  for all destructors, assume the first n arguments are of kind term, then apply the inductive hypothesis on those arguments and then backchain with the progress lemma.
			NEW GENERAL RULE: an argument can be checked for "value" in the operational semantics ONLY if it a contextual argument. 
			IF it is a contextual argument, BUT not checked for "value" in the operational semantics, THEN "progresses" is not necessary for that argument. 
		  *)