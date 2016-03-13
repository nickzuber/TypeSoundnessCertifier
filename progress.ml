open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Proof
open CanonicalForms

let dynamicSemantics = "step"
let toE i = "E" ^ (string_of_int i)
let toPrgsE i = "PrgsE" ^ (string_of_int i)
let toTypeOfE i = "TypeOfE" ^ (string_of_int i)
let progressImplication var = "progresses " ^ var ^ " -> "

let combinatoricsOfSearches sensitivePositions errorSpec = 
	let multiply = if is_none errorSpec then 1 else 2 in 
		repeat (Tactic(Search)) (((List.length sensitivePositions) * multiply) + 1)

let combinatoricsWithErrorAnalysis = [Tactic(Search) ; Tactic(Case("ProgressClause")) ; Tactic(Search) ; Tactic(Search)]

let progressDefinition sl = 
	if (sl_containErrors sl) 
	then "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := {error E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."
	else "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."

let appealToCanonicalForm typeSpec = 
	let constructors = (specType_getConstructors typeSpec) in 
	let typeBeingProved = (specType_getTypeName typeSpec) in 
	let caseCanonicalIfNecessary = if List.length constructors = 1 then Qed else Tactic(Case("Canonical")) in 
  [Tactic(Named("Canonical", Apply("canonical_form_" ^ typeBeingProved, [(toTypeOfE 1) ; "ProgressClause"]))) ; caseCanonicalIfNecessary ; RepeatPlain((List.length constructors) - 1, Tactic(Search))] 

let preambleproof_progress_lemmas sensitivePositionsRaw = let sensitivePositions = List.map toPrgsE sensitivePositionsRaw in if sensitivePositions = [] then Qed else Seq([Tactic(Intros("Main" :: sensitivePositions)) ; Tactic(Named((toTypeOfE 1), Case("Main"))) ; Tactic(Named("ProgressClause", Case((List.hd sensitivePositions))))] @ List.map toCase (List.tl sensitivePositions))

let statement_progress_lemmas termDecl sensitivePositions = 
	let extraPremise = String.concat "" (List.map progressImplication (List.map toE sensitivePositions)) in 
	let (canonical, vars) = term_getCanonical termDecl in 
	"Theorem progress_" ^ (term_getOperator termDecl) ^ " : forall" ^ toStringFromList vars ^ " T, {typeOf (" ^ toString canonical ^ ") T} -> " ^ extraPremise ^ "progresses (" ^ toString canonical ^ ")." 

let progressLemmasByOperators errorSpec typeSpec eliminator =  
	let termDecl = specTerm_getSig eliminator in 
	let sensitivePositions = (term_getValPositions termDecl) in 
	let theorem  = statement_progress_lemmas termDecl sensitivePositions in 	
	let preamble = preambleproof_progress_lemmas sensitivePositions in 
	let proof_appealToCanonicalForm = if is_none typeSpec then [] else appealToCanonicalForm (get typeSpec) in 
	let proof = proof_appealToCanonicalForm @ combinatoricsOfSearches sensitivePositions errorSpec 
		in Theorem(theorem, Seq([preamble ; Seq(proof)])) 

let progressLemmasByErrorHandler errorHandler = 
	let termDecl = specTerm_getSig errorHandler in 
	let sensitivePositions = term_getValPositions termDecl in 
	let theorem  = statement_progress_lemmas termDecl sensitivePositions in 	
	let preamble = preambleproof_progress_lemmas sensitivePositions in 
	let proof = combinatoricsWithErrorAnalysis  
		in Theorem(theorem, Seq([preamble ; Seq(proof)])) 
			
let progressLemmasTypes errorSpec typeSpec = 
	List.map (progressLemmasByOperators errorSpec None) (specType_getConstructors typeSpec)
		@
	List.map (progressLemmasByOperators errorSpec (Some typeSpec)) (specType_getEliminators typeSpec)

(* returns progressDef, (theorem, proof) list *)

let generateProgressLemmas sl = match sl with SafeTypedLanguage(types, others, errorSpec) -> 
	let progressLemmasForErrorRelated = if is_none errorSpec then [] else List.map progressLemmasByErrorHandler (specError_getHandlers errorSpec) @ [(progressLemmasByOperators errorSpec None) (specError_getError errorSpec)] in 
 	   List.concat (List.map (progressLemmasTypes errorSpec) types) @ List.map (progressLemmasByOperators errorSpec None) others @ progressLemmasForErrorRelated

let callProgressLemma operator = let termDecl = specTerm_getSig operator in Seq([ForEach(List.map toTypeOfE (term_getValPositions termDecl), Tactic(Apply("IH", ["x"]))) ; Tactic(Backchain("progress", term_getOperator termDecl))])

let generateProgressTheorem sl = match sl with SafeTypedLanguage(types, others, errorSpec) -> 
         let theorem = "Theorem progress : forall E T, {typeOf E T} -> progresses E. \ninduction on 1. intros Main. TypeOfE1 : case Main." in
		 let proofConstructors = Seq(List.map callProgressLemma (List.concat (List.map specType_getConstructors types))) in 
		 let proofEliminators = Seq(List.map callProgressLemma (List.concat (List.map specType_getEliminators types))) in 
         let proofOthers = Seq(List.map callProgressLemma others) in
		 let proofErrors = if is_none errorSpec then Qed else Seq(List.map callProgressLemma ((specError_getHandlers errorSpec) @ [specError_getError errorSpec])) in 
          Theorem(theorem, Seq([proofConstructors ; proofEliminators ; proofOthers ; proofErrors]))

		  (*			
		  (*
			  
			  
			  OLD call to canonical form is silly:
		  [Tactic(Named("Canonical", Assert(String.concat " \\/ " (List.map (existentiallyClosedEquation "E1") constructors)))) ; Tactic(Backchain("canonical_form", typeBeingProved)) ; Tactic(Case("Canonical")) ; RepeatPlain((List.length constructors) - 1, Tactic(Search))] 
			  	
Seq([Tactic(Case("Value"))] @ List.map callCanonicalLemma (specError_getHandlers errorSpec)) 
			  
let progressLemmasByOperators errorSpec operator = 
	let termDecl = specTerm_getSig operator in 
	let sensitivePositions = List.map toE (term_getValPositions termDecl) in 
	let theorem  = statement_progress_lemmas termDecl sensitivePositions in 	
	let preamble = preambleproof_progress_lemmas sensitivePositions in 
	let proof = combinatoricsOfSearches sensitivePositions errorSpec 
		in Theorem(theorem, Seq([preamble ; Seq(proof)])) 	

let progressLemmasEliminators errorSpec typeSpec eliminator =  
	let termDecl = specTerm_getSig eliminator in 
	let sensitivePositions = List.sort_uniq (String.compare) ("E1" :: List.map toE (term_getValPositions termDecl)) in 
	let theorem  = statement_progress_lemmas termDecl sensitivePositions in 	
	let preamble = try preambleproof_progress_lemmas sensitivePositions with Failure _ -> raise(Failure("eliminator")) in 
	let proof = appealToCanonicalForm typeSpec @ [Tactic(Search)] @ combinatoricsOfSearches (List.drop 1 sensitivePositions) errorSpec
		in Theorem(theorem, Seq([preamble ; Seq(proof)])) 


Case(List.hd positions_of_values)

let proofByLemma termSpec = match specTerm_getSig termSpec with DeclTrm(c, ctx, arguments) -> Tactic(Backchain("progress", c))

let proofOrindaryTerm termSpec = match specTerm_getSig termSpec with DeclTrm(c, ctx, arguments) -> 
	if ctx_emptyContext ctx then Tactic(Search) else proofByLemma termSpec


let toE i = "E" ^ (string_of_int i)
			  
(*  let rec toString term = match term with 
    | Var(name) -> name
    | Constructor(name, arguments) -> name ^ " " ^ String.concat " " (List.map toString arguments)
*)
  
	
	match summary with (termDecl, firstIsExhaustive) -> 
	let sensitivePositions = grid_getSensitivePositions grid in 
	let theorem  = statement_progress_lemmas termDecl sensitivePositions in 	
	let preamble = preambleproof_progress_lemmas sensitivePositions in 
	let proof = 
		match List.hd grid with 
			| Free -> combinatoricsOfSearches sensitivePositions errorSpec
			| Value -> combinatoricsOfSearches sensitivePositions errorSpec
			| ExhaustiveCases cases -> appealToCanonicalForm cases @ combinatoricsOfSearches sensitivePositions errorSpec
		in Theorem(theorem, Seq([preamble ; Seq(proof)])) 
  
			  
	let closeWithSearches = if getErrors signatureTerms = [] then repeat (Tactic(Search)) (List.length (List.drop 1 valuePositions)) else repeat (Tactic(Search)) ((List.length (List.drop 1 valuePositions)) * 2) in 
			  
	let possibleErrorCase = if is_none errorSpec then [] else if List.mem termDecl (getErrorHandlers signatureTerms) then [Tactic(Case("ProgressClause")) ; Tactic(Search)] else [Tactic(Search)] in 
		  	Alrogithm for progress lemma for constructors: search.
		  	Alrogithm for progress lemma for destructors: case E1, appeal to canonical form, and for all canonical forms do search. then do search for the progress case (when E1 progresses)

Seq(repeat (Tactic(Search)) (List.length (getConstructors signatureTerms) - List.length (getValuesWithValues signatureTerms))) in 
	(List.map (progressLemmasValues (not (getErrors signatureTerms = []))) (getValuesWithValues signatureTerms)) @ (List.map (progressLemmas signatureTerms) (getNonResults signatureTerms)) 
			  		  *)
			  
signatureTerms termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> 
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

			  
			  
			    
Seq(List.map proofBycases ((getValuesWithValues signatureTerms) @ (getNonResults signatureTerms))) 
			           let proofBycases = (fun termDecl -> let valuePositions = List.map toE (termDelc_getCtxInfo termDecl) in if termDecl_containTerms termDecl then Seq([ForEach(valuePositions, Tactic(Apply("IH", ["x"]))) ; Tactic(Backchain("progress", termDelc_getOperator termDecl))]) else Tactic(Backchain("progress", termDelc_getOperator termDecl))) in
			  
		  	Alrogithm for main progress:
			  for all constructors: search.
			  for all destructors, assume the first n arguments are of kind term, then apply the inductive hypothesis on those arguments and then backchain with the progress lemma.
			NEW GENERAL RULE: an argument can be checked for "value" in the operational semantics ONLY if it a contextual argument. 
			IF it is a contextual argument, BUT not checked for "value" in the operational semantics, THEN "progresses" is not necessary for that argument. 
		  *)