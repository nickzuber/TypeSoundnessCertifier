
open Type_system
open Aux
open Terms

let eachCanonicalForm values numberOfDeconstructors signatureEntry = match signatureEntry with DeclType(c,kind,constructors,deconstructors,arguments) ->
         let termConstructors = List.map getTermInInput (List.map getConclusion (List.filter (onlyRulesOfOutput c) values)) in 
         let newVars = (Aux.getFormalVariables "T" (List.length arguments)) in
         let universalQuantificationOnArguments = "forall E " ^ String.concat " " newVars ^ ", " in
         let formalOfType = "(" ^ c ^ " " ^ String.concat " " newVars ^ ")" in
         let existentialQuantificationOnArguments =  fun termConstructor -> let aa = (List.map toStringWith' (getArgumentsOfConstructor termConstructor)) in if aa = [] then "E = " ^ (toStringWith' termConstructor) else "exists " ^ String.concat " " aa ^ ", E = " ^ (toStringWith' termConstructor) in 
         let theorem =  "Theorem " ^ " canonical_form_" ^ c ^ " : " ^ universalQuantificationOnArguments ^ "{typeOf E " ^ formalOfType ^ "} -> {value E} -> " ^ String.concat " \\/ " (List.map existentialQuantificationOnArguments termConstructors) ^ ".\n" in
         let searches = (fun term -> "search.") in
         let preamble = "intros Main Value. case Main. \n" in
         let proof = " " ^ (String.concat " " (List.map searches termConstructors)) ^ "\n" in
         let dismissedCases = " " ^ (String.concat " " (Aux.repeat "case Value." numberOfDeconstructors)) ^ "\n" in 
         theorem ^ preamble ^ proof ^ dismissedCases

let generateCanonicalFormsLemma ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let values = List.filter (onlyTypingRulesOfValues signatureTypes) rules in
         let numberOfDeconstructors = List.length (getDeConstructorFromTypeSignature signatureTypes) in
         String.concat "\n" (List.map (eachCanonicalForm values numberOfDeconstructors) signatureTypes)



(*          match rule with Rule(name,premises,conclusion) ->
	    let subproofByValue = (fun constructorToProve -> if constructorToProve == constructor then "search.\n" else "case H1\n.") in 
         let mainproof = String.concat " " (List.map subproofByValue (List.map getConstructorInInput (List.map getConclusion values))) in 
*)

