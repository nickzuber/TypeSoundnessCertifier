
open Type_system
open Aux
open Terms
open Proof

let eachCanonicalForm values numberOfDeconstructors signatureEntry = match signatureEntry with DeclType(c,kind,constructors,deconstructors,arguments) ->
         let termConstructors = List.map getTermInInput (List.map getConclusion (List.filter (onlyRulesOfOutput c) values)) in 
         let newVars = (Aux.getFormalVariables "T" (List.length arguments)) in
         let universalQuantificationOnArguments = "forall E " ^ String.concat " " newVars ^ ", " in
         let formalOfType = "(" ^ c ^ " " ^ String.concat " " newVars ^ ")" in
         let existentialQuantificationOnArguments =  fun termConstructor -> let aa = (List.map toStringWith' (getArgumentsOfConstructor termConstructor)) in if aa = [] then "E = " ^ (toStringWith' termConstructor) else "exists " ^ String.concat " " aa ^ ", E = " ^ (toStringWith' termConstructor) in 
         let theorem =  "Theorem " ^ " canonical_form_" ^ c ^ " : " ^ universalQuantificationOnArguments ^ "{typeOf E " ^ formalOfType ^ "} -> {value E} -> " ^ String.concat " \\/ " (List.map existentialQuantificationOnArguments termConstructors) ^ "." in
         let preamble = createSeq([Intros(["Main" ; "Value"]) ; Case("Main")]) in
         let proof = Seq([RepeatPlain(List.length termConstructors, Tactic(Search))]) in
         let dismissedCases = Seq([RepeatPlain(numberOfDeconstructors, Tactic(Case("Value")))]) in 
          Theorem(theorem, Seq([preamble ; proof ; dismissedCases]))

(* this function below returns a list of Theorem(theorem,proof) *)
let generateCanonicalFormsLemma ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let values = List.filter (onlyTypingRulesOfValues signatureTypes) rules in
         let numberOfDeconstructors = List.length (getDeConstructorFromTypeSignature signatureTypes) in
          (List.map (eachCanonicalForm values numberOfDeconstructors) signatureTypes)



(*          match rule with Rule(name,premises,conclusion) ->
	    let subproofByValue = (fun constructorToProve -> if constructorToProve == constructor then "search.\n" else "case H1\n.") in 
         let mainproof = String.concat " " (List.map subproofByValue (List.map getConstructorInInput (List.map getConclusion values))) in 
*)

