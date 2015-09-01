
open Batteries
open Type_system
open Terms
open Proof

let getInfo typingRules signatureTerms term = 
		 let typeRuleOriginal = try List.hd (lookupRuleByConstructor (getConstructor term) typingRules) with | Failure "hd" -> raise (Failure ("not in typing rules: " ^ (toString term))) in
		 let firstArgument = try List.hd (getArgumentsOfConstructor term) with | Failure "hd" -> (Var("fake")) in (* raise (Failure ("no first argument in : " ^ (toString term))) *)
		 let abstractionsOriginalTerm = getNumberOfAbstractionsByConstr (getConstructor term) signatureTerms in 
		  (term, typeRuleOriginal, firstArgument, abstractionsOriginalTerm)

let originalTerm info = match info with (a, b, c, d) -> a
let typeRuleOriginal info = match info with (a, b, c, d) -> b
let firstArgument info = match info with (a, b, c, d) -> c
let hasAbstractions info = match info with (a, b, c, d) -> d > 0

let maybeSubstitutionLemmaBeforeSearch typingRules signatureTerms rule = match rule with Rule(name, premises, conclusion) ->
		 let infoTopTerm = getInfo typingRules signatureTerms (getTermInInput conclusion) in 
		 let eitherSelfOrArg = fun info -> fun arg -> let (m,n) = (deBrujinStyleIndex arg (originalTerm infoTopTerm) (0,0)) in if m = 0 then "TypeOf" else "Arg" ^ (string_of_int m) ^ "_" ^ (string_of_int n) in
		 let ifHypotheticalAlsoCut = fun info -> fun arg -> (typeOfPremiseForVariable (firstArgument info) (typeRuleOriginal info)) = 1 in 
		 let appealToSubstitutionLemma = fun i -> fun info -> fun arg -> let argHyp = "Arg" ^ (string_of_int i) ^ "_1" in if (ifHypotheticalAlsoCut info arg) then Tactic(InstAndCut(argHyp, (toString arg),(eitherSelfOrArg info arg))) else Tactic(Inst(argHyp, (toString arg))) in 
		 let secondOp = let infoNestedTerm = getInfo typingRules signatureTerms (firstArgument infoTopTerm) in 
			 if (not (hasAbstractions infoNestedTerm)) then Qed else appealToSubstitutionLemma 2 infoNestedTerm (retrieveApplication (originalTerm infoNestedTerm) signatureTerms (getTermInOutput conclusion)) in
                  secondOp 

let generatePreservationTheorem ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let numberOfreductionRules = (List.length (List.filter onlyStepRules rules)) - (List.length (List.filter onlyContextRules rules)) in
         let reductionRules = List.take numberOfreductionRules (List.filter onlyStepRules rules) in 
         let contextRules = List.drop numberOfreductionRules (List.filter onlyStepRules rules) in 
         let typingRules = (List.filter onlyTypingRules rules) in 
         let theorem = "Theorem preservation : forall E E' T, {step E E'} -> {typeOf E T} -> {typeOf E' T}." in 
		 let preamble = createSeq([Induction(1) ; Intros(["Main" ; "TypeOf"]) ; Named("Step", Case("Main"))]) in
         let subProofReduction = (fun rule -> Seq([Tactic(Named("Arg1_1", CaseKeep("TypeOf"))) ; Tactic(Named("Arg2_1", Case("Arg1_1"))) ; ((maybeSubstitutionLemmaBeforeSearch typingRules) signatureTerms rule) ; Tactic(Search)])) in
         let subProofContextual = (fun rule -> match rule with Rule(name,premises,conclusion) -> let hypByArgIndex = "TypeOf" ^ (String.right name 1) in createSeq [Named("TypeOf1", Case("TypeOf")) ; Apply("IH", ["Step" ; hypByArgIndex]) ; Search]) in
         let proofReductions = (List.map subProofReduction reductionRules) in
         let proofContextual = (List.map subProofContextual contextRules) in
            Theorem(theorem, Seq(List.append (preamble::proofReductions) proofContextual))
