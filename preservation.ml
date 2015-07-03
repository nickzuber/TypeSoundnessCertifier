
open Batteries
open Type_system
open Terms

let getInfo typingRules signatureTerms term = 
		 let typeRuleOriginal = try List.hd (lookupRuleByConstructor (getConstructor term) typingRules) with | Failure "hd" -> raise (Failure ("not in typing rules: " ^ (toString term))) in
		 let firstArgument = try List.hd (getArgumentsOfConstructor term) with | Failure "hd" -> (Var("fake")) in (* raise (Failure ("no first argument in : " ^ (toString term))) *)
		 let abstractionsOriginalTerm = getNumberOfAbstractionsByConstr (getConstructor term) signatureTerms in 
		  (term, typeRuleOriginal, firstArgument, abstractionsOriginalTerm)

let originalTerm info = match info with (a, b, c, d) -> a
let typeRuleOriginal info = match info with (a, b, c, d) -> b
let firstArgument info = match info with (a, b, c, d) -> c
let hasAbstractions info = match info with (a, b, c, d) -> d > 0

(* 
let maybeSubstitutionLemmaBeforeSearch typingRules signatureTerms rule = match rule with Rule(name, premises, conclusion) ->
		 let infoTopTerm = getInfo typingRules signatureTerms (getTermInInput conclusion) in 
		 let eitherSelfOrArg = fun info -> fun arg -> let (m,n) = (deBrujinStyleIndex arg (originalTerm infoTopTerm) (0,0)) in if m = 0 then "TypeOf" else "Arg" ^ (string_of_int m) ^ "_" ^ (string_of_int n) in
let ifHypotheticalAlsoCut = fun info -> fun arg -> if (typeOfPremiseForVariable (firstArgument info) (typeRuleOriginal info)) = 1 then " cut ToCut with " ^ (eitherSelfOrArg info arg) ^ "." else "" in 
		 let appealToSubstitutionLemma = fun i -> fun info -> fun arg -> let argHyp = "Arg" ^ (string_of_int i) ^ "_1" in "ToCut : inst " ^ argHyp ^ " with n1 = " ^ toString arg ^ "." ^ (ifHypotheticalAlsoCut info arg) in 
		 let (firstOp, finished) = if not (hasAbstractions infoTopTerm) then ("Arg2_1 : case Arg1_1.", false) else (appealToSubstitutionLemma 1 infoTopTerm (retrieveApplication (originalTerm infoTopTerm) signatureTerms (getTermInOutput conclusion)), true) in
		 let secondOp = (if finished then "" else 
	            let infoNestedTerm = getInfo typingRules signatureTerms (firstArgument infoTopTerm) in 
			 " " ^  if (not (hasAbstractions infoNestedTerm)) then "case Arg2_1." else appealToSubstitutionLemma 2 infoNestedTerm (retrieveApplication (originalTerm infoNestedTerm) signatureTerms (getTermInOutput conclusion))) in
                  firstOp ^ secondOp 
*)

let maybeSubstitutionLemmaBeforeSearch typingRules signatureTerms rule = match rule with Rule(name, premises, conclusion) ->
		 let infoTopTerm = getInfo typingRules signatureTerms (getTermInInput conclusion) in 
		 let eitherSelfOrArg = fun info -> fun arg -> let (m,n) = (deBrujinStyleIndex arg (originalTerm infoTopTerm) (0,0)) in if m = 0 then "TypeOf" else "Arg" ^ (string_of_int m) ^ "_" ^ (string_of_int n) in
let ifHypotheticalAlsoCut = fun info -> fun arg -> if (typeOfPremiseForVariable (firstArgument info) (typeRuleOriginal info)) = 1 then " cut ToCut with " ^ (eitherSelfOrArg info arg) ^ "." else "" in 
		 let appealToSubstitutionLemma = fun i -> fun info -> fun arg -> let argHyp = "Arg" ^ (string_of_int i) ^ "_1" in " ToCut : inst " ^ argHyp ^ " with n1 = " ^ toString arg ^ "." ^ (ifHypotheticalAlsoCut info arg) in 
		 let secondOp = let infoNestedTerm = getInfo typingRules signatureTerms (firstArgument infoTopTerm) in 
			 if (not (hasAbstractions infoNestedTerm)) then "" else appealToSubstitutionLemma 2 infoNestedTerm (retrieveApplication (originalTerm infoNestedTerm) signatureTerms (getTermInOutput conclusion)) in
                  secondOp 

let generatePreservationTheorem ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let onlyDeConstructors = getDeConstructorFromTypeSignature signatureTypes in
         let numberOfreductionRules = (List.length (List.filter onlyStepRules rules)) - (List.length (List.filter onlyContextRules rules)) in
         let reductionRules = List.take numberOfreductionRules (List.filter onlyStepRules rules) in 
         let contextRules = List.drop numberOfreductionRules (List.filter onlyStepRules rules) in 
         let typingRules = (List.filter onlyTypingRules rules) in 
         let theorem = "Theorem preservation : forall E E' T, {step E E'} -> {typeOf E T} -> {typeOf E' T}. induction on 1. intros Main TypeOf. Step : case Main.\n" in
         let subProofReduction = (fun rule -> "Arg1_1 : case TypeOf (keep). Arg2_1 : case Arg1_1." ^ ((maybeSubstitutionLemmaBeforeSearch typingRules) signatureTerms rule) ^ " search. \n") in
         let subProofContextual = (fun rule -> match rule with Rule(name,premises,conclusion) -> let hypByArgIndex = "TypeOf" ^ (String.right name 1) in "TypeOf1 : case TypeOf. apply IH to Step " ^ hypByArgIndex ^ ". search.\n") in
         let proofReductions = String.concat "" (List.map subProofReduction reductionRules) in
         let proofContextual = String.concat "" (List.map subProofContextual contextRules) in
            theorem ^ proofReductions ^ proofContextual
         
