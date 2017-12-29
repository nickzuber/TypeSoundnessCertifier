
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open Proof 
open ListManagement
open GenerateLambdaProlog

let inversion_subtype_NAME = "inversion_subtype"
let inversion_typing_NAME = "inversion_typing"
let inversion_error_NAME = inversion_typing_NAME ^ "_error"

let subtype = "subtype"
let reflexivity = [Rule("subtype_refl", [], Formula(subtype, [Var("T") ; Var("T")], []))]
let transitivity = [Rule("subtype_trans", [Formula(subtype, [Var("T1") ; Var("T2")], []) ; Formula(subtype, [Var("T2") ; Var("T3")], [])], Formula(subtype, [Var("T1") ; Var("T3")], []))]
let subsumption = [Rule("subsumption", [Formula("typeOf", [Var("E")], [Var("S")]) ;  Formula(subtype, [Var("S") ; Var("T")], [])], Formula("typeOf", [Var("E")], [Var("T")]))]

let subsumption_in_contexts_NAME = "subsumption_in_contexts"
let subsumption_in_contexts_lemma = Theorem("Theorem " ^ subsumption_in_contexts_NAME ^ ": forall T1 T2, {subtype T1 T2} -> nabla x, {subtype x T1 |- subtype x T2}. ", Seq([Tactic(Intros []) ; Tactic(Search)]))

let subtyping_IsForAList ldl (c, rule) = (ldl_contains_lists ldl c)
let subtyping_IsNotForAList ldl pair = not (subtyping_IsForAList ldl pair)
let subtyping_getRulesForNoLists ldl subtyping = 
	  List.filter (subtyping_IsNotForAList ldl) (subtyping_getRules subtyping)
(* This below returns only the relevant subtyping for lists.. so it discards the one for empty *)
let subtyping_getRulesForLists ldl subtyping = List.filter (fun (c,rule) -> not (rule_getPremises rule = [])) (List.filter (subtyping_IsForAList ldl) (subtyping_getRules subtyping))

let subtyping_widthRule c = Rule(c  ^ "_width", [], Formula(subtype, [Constructor(c ^ "T", [Constructor(consListT c, [Var "L" ; Var "T" ; Var "Rest"])]) ; Constructor(c ^ "T", [Constructor(emptyListT c,[])])], []))
let subtyping_emptyList_association c = 
	(c ^ "T", 
	Rule(c  ^ "_empty", [], Formula(subtype, [Constructor(c ^ "T", [Constructor(emptyListT c,[])]) ; Constructor(c ^ "T", [Constructor(emptyListT c,[])])], []))
	)

let subtyping_isWidthSubtyping subtyping c = 
	let widthRule = (List.filter (fun (c2, (Rule(name, _, _))) -> ((c2 = c) && (String.exists name "width"))) (subtyping_getRules subtyping)) in not (widthRule = []) 
(*	raise(Failure((dump subtyping) ^ "-----" ^ (dump (List.filter (fun (c2, (Rule(name, _, _))) -> ((c2 = c) && (String.exists name "width"))) (subtyping_getRules subtyping))))) 
String.ends_with*)	
let rec renameClashesWithPrefix str vars term = match term with 
| Var(variable) -> if List.mem (Var(variable)) vars then Var(str ^ variable) else Var(variable)
| Constructor(name, arguments) -> Constructor(name, List.map (renameClashesWithPrefix str vars) arguments)
 
let type_getVariance i typeEntry varianceByPosition = 
	if entry_isAbstraction typeEntry 
	 then try List.assoc i varianceByPosition with _ -> Normal 
	 else try List.assoc i varianceByPosition with _ -> Cov 

let premiseBasedOnVariance_ variance var1 var2 = 
	match variance with 
	| Cov -> Formula(subtype, [var1 ; var2], [])
	| Contra -> Formula(subtype, [var2 ; var1], [])
	| Inv -> Formula("equal", [var1 ; var2], [])
	| Normal -> Generic(Formula(subtype, [Application(var1, Bound("x")) ; Application(var2, Bound("x"))], []))
	| Rec -> raise(Failure("Recursive subtyping is currently not supported"))

(* this function below is plural, premiseS *)
let subtyping_by_variance ldl (c, varianceByPosition) = 
	let typeDecl = specType_getSig (ldl_lookup_typeSpec ldl c) in 
	let arguments = type_getArguments typeDecl in 
	let vars = getFormalVariables "T" (List.length (type_getArguments typeDecl)) in 
	let variables = List.map toVar vars in 
	let variablesTicked = List.map toVar (List.map var_ticked vars) in 
	let premiseBasedOnVariance i typeEntry = 
		(let variance = type_getVariance i typeEntry varianceByPosition in 
		 premiseBasedOnVariance_ variance (List.nth variables i) (List.nth variablesTicked i)) in 
	  if typeDecl_isList typeDecl then 
		  let original_c = (chop_last_char c 'T') in 
	  (c, Rule("subtype_" ^ c,
	  		[premiseBasedOnVariance 0 (Simple(Inv, "")) ; (* Simple, just because List acts like Simple for default variance, i.e. unless specified we want them to be covariant. Inv is there only to put something and give a well-typed thing *)
			Formula(subtype, [Constructor(c, [Var "Rest1"]) ; Constructor(c, [Var "Rest1'"])], [])], 
			Formula(subtype, [Constructor(c, [Constructor(consListT original_c, [Var "L" ; Var "T1" ; Var "Rest1"])]) ; Constructor(c, [Constructor(consListT original_c, [Var "L" ; Var "T1'" ; Var "Rest1'"])])], [])  (* Notice that L is the same in both sides *)
		))
  		else 
	  (c, Rule("subtype_" ^ c, 
		 	List.mapi premiseBasedOnVariance arguments, 
			Formula(subtype, [Constructor(c, variables) ; Constructor(c, variablesTicked)], []))) 
	
let subtyping_expand ldl subtyping = 
	if is_none subtyping then None else 
		let Subtyping(top, varianceList, otherRules) = get subtyping in 
		let topTaken = if is_none top then [] else [get top] in 
		let chopT c = (chop_last_char c 'T') in 
		let axiomsForEmptyListIfNeeded = List.map subtyping_emptyList_association (List.map chopT (ldl_getLists_names ldl)) in 
		let onlyIfItIsNotList c = not (ldl_contains_lists ldl c) in 
		let addTheRest varianceList = varianceList @ (List.map (fun c -> (c, [])) (list_difference (List.map specType_getTypeName (ldl_getTypes ldl)) (List.map fst varianceList @ (List.filter onlyIfItIsNotList (List.map fst otherRules)) @ topTaken))) in 
		 Some(Subtyping(top, varianceList, List.map substitute_equalities (List.map (subtyping_by_variance ldl) (addTheRest (getAllArrangedByKey varianceList))) @ axiomsForEmptyListIfNeeded @ otherRules)) 

let subtyping_declaration subtyping = if is_some subtyping then "type subtype typ -> typ -> o.\n" else ""
let subtyping_definition ldl subtyping = 
	if is_none subtyping then [] else 
		let Subtyping(top, varianceList, otherRules) = get subtyping in 
		let subtyping_for_top top = if is_none top then [] else let c = get top in [Rule("subtype_top", [], Formula(subtype, [toVar "T" ; Constructor(c, [])], []))] in 
		subtyping_for_top top @ List.map snd otherRules @ reflexivity @ transitivity @ subsumption 
								(*	here the variance have been already expanded, so all the subtyping rules are in otherRules *)
let is_backed rule premise = if formula_isHypothetical premise 
								then let typToCheck = formula_getLastArgument (formula_getHypotheticalPart premise) in is_some (rule_lookup_premise_by_var rule typToCheck)
								else true
let rec fillWithReflexiveSubtyping rule premise = if is_backed rule premise then [premise] else 
	let typNotBacked = formula_getLastArgument (formula_getHypotheticalPart premise) in [Formula(subtype, [typNotBacked ; typNotBacked], []) ; premise] 

let inversion_subtype ldl (typeOperator, rule) = 
	let conclusion = rule_getConclusion rule in 
	let premises = rule_getPremises rule in 
	let [lesser ; greater] = formula_getInputs conclusion @ formula_getOutputs conclusion in 
	let greaterBackup = greater in 
	let greater = if ldl_contains_lists ldl typeOperator then Constructor(typeOperator, [Var "List"]) else greater in 
	let varsOfLesser = List.map toString (term_getVariables lesser) in 
	let varsOfGreater = List.map toString (term_getVariables greater) in 
	let varsOfGreaterBackup = if ldl_contains_lists ldl typeOperator then List.map toString (term_getVariables greaterBackup) else [] in 
	let varsToExistentiallyQuantify = removeDuplicates ((list_difference varsOfLesser varsOfGreater) @ varsOfGreaterBackup) in 
	(* it is fine that varsToExistentiallyQuantify contains the vars of greater even if we use another one, because those must be quantified anyway for List = ... *)
	let nablaQuantification = if List.exists formula_isWithContext premises then "nabla x, " else "" in 
	let premisesFinal = List.concat (List.map (fillWithReflexiveSubtyping rule) premises) in 
	let addTheOrEmptyIfItIsList = if ldl_contains_lists ldl typeOperator then " (exists List', Typ = " ^ (generateTerm (Constructor(typeOperator, [Var "List'"]))) ^ " /\\ List = " ^ generateTerm (Constructor(emptyListT typeOperator, [])) ^ ") \\/ " else "" in 
	let addListIsGreaterBackup = if ldl_contains_lists ldl typeOperator then " /\\ List = " ^ (generateTerm (term_getNestedFirstArgument greaterBackup)) ^ " " else "" in 
	let theorem = "Theorem " ^ inversion_subtype_NAME ^ "_" ^ typeOperator ^ " : " ^ universalQuantification ("Typ"::varsOfGreater) ^ "{subtype Typ " ^ (generateTerm greater) ^ "} -> " ^ addTheOrEmptyIfItIsList ^ "(" ^ existentialQuantification varsToExistentiallyQuantify ^ nablaQuantification ^ " Typ = " ^ (generateTerm lesser) ^ addListIsGreaterBackup ^ generateANDformula premisesFinal ^ ").\n" in 
	let preamble = "induction on 1. intros Main. Subtype1 : case Main(keep). \n" in 
	let adjustmentsForHypothetical n = 
		let n = if is_backed rule (nthMinusOne premises n) then n else n + 1 in 
		let i = string_of_int n in let iminus = string_of_int (n-1) in Seq([Tactic(Named("New" ^ iminus, Apply(subsumption_in_contexts_NAME, ["Arg_2_" ^ iminus]))) ; Tactic(Cut("Arg_1_" ^ i,"New" ^ iminus))])  in 
	let proofReflexiveCase = 
		if ldl_contains_lists ldl typeOperator 
			then [Seq([Tactic(Named("Cases", Apply(memberCasesLemma typeOperator, ["Main"]))) ; Tactic(Case("Cases")) ; Tactic(Search) ; Tactic(Search)])]
		    else [Seq([Tactic(Search)])] 
		in 
	let proofTransitiveCase = 
		if ldl_contains_lists ldl typeOperator 
			then [Seq([Tactic(Named("Arg_2_1", Apply("IH", ["Subtype2"]))) ; 
		               Tactic(Case("Arg_2_1")) ; 
						  Tactic(Named("Arg_1_1",Apply("IH", ["Subtype1"])))] @ List.map adjustmentsForHypothetical (findIndicesByPred formula_isHypothetical premises) @ [Tactic(Case("Arg_1_1")) ; Tactic(Search)  ; Tactic(Search) ;
						  Tactic(Named("Arg_1_1",Apply("IH", ["Subtype1"])))] @ List.map adjustmentsForHypothetical (findIndicesByPred formula_isHypothetical premises) @ [Tactic(Case("Arg_1_1")) ; Tactic(Search) 
					])
			  	  ] 
  			else [Seq([Tactic(Named("Arg_2_1", Apply("IH", ["Subtype2"]))) ; Tactic(Named("Arg_1_1",Apply("IH", ["Subtype1"])))] @ List.map adjustmentsForHypothetical (findIndicesByPred formula_isHypothetical premises) @ [Tactic(Search)])] 
		in 
	let proofSpecificCaseFromDefinition = 
		if ldl_contains_lists ldl typeOperator 
			then [Seq([Tactic(Search) ; Tactic(Search)])] 
			else [Seq([Tactic(Search)])] in 
	 (premisesFinal, Theorem(theorem ^ preamble, Seq(proofSpecificCaseFromDefinition @ proofReflexiveCase @ proofTransitiveCase)))		
	
let inversion_typing subtypingRules termSpec = 
	let op = term_getOperator (specTerm_getSig termSpec) in 	
	let typingRule = specTerm_getTyping termSpec in 
	let premisesTyp = rule_getPremises typingRule in 	
	let conclusionTyp = rule_getConclusion typingRule in 
	let term = formula_getFirstInput conclusionTyp in 
	let typ = formula_getFirstOutput conclusionTyp in 
	let typOperator = term_getConstructor typ in 
	let subtypingRule = try List.assoc typOperator subtypingRules with _ -> raise (Failure("no subtyping rule for " ^ op))  in 
	let premisesSub = fst (inversion_subtype emptyLDL (typOperator, subtypingRule)) in 	
	let conclusionSub = rule_getConclusion subtypingRule in 
	let [lesser ; greater] = formula_getInputs conclusionSub @ formula_getOutputs conclusionSub in 
	let greaterIneed = term_AllwithTick lesser in 
(*	let typeFact = Formula(typing, [term], [greater]) in *)
	let typeFact = Formula(typing, [term], [greaterIneed]) in 
	let variablesInCommon = list_difference (term_getArguments greater) (list_difference (term_getArguments greater) (term_getArguments lesser)) in 
	let catchUpToGreater =  List.combine variablesInCommon (List.map toTicked variablesInCommon) in 
	let premisesSubGreaterToGreaterNeed = List.map toEqual catchUpToGreater @ List.map (formula_substitutions catchUpToGreater) premisesSub in 		
(*	let associationGreaterToGreaterNeed = List.combine (term_getArguments greater) (term_getArguments greaterIneed) in 
	let premisesSubGreaterToGreaterNeed = List.map (formula_substitutions associationGreaterToGreaterNeed) premisesSub 	
*)	let associationToSubstitute = List.combine (term_getArguments lesser) (term_getArguments typ) in 	
	let premisesSubSubstituted = List.map (formula_substitutions associationToSubstitute) premisesSubGreaterToGreaterNeed in 
	let varsIntypeFact = (removeDuplicates (formula_getAllVariables typeFact)) in 
	let varsInPremises = removeDuplicates (List.concat (List.map formula_getAllVariables (premisesTyp @ premisesSubSubstituted))) in 
	let varsLeftOvers = list_difference varsInPremises varsIntypeFact in 
	let theoremPreamble = "Theorem " ^ inversion_typing_NAME ^ "_" ^ op ^ " : " ^ universalQuantification (List.map generateTerm varsIntypeFact) in 
	let nablaQuantification = if List.exists formula_isWithContext (premisesTyp @ premisesSubSubstituted) then "nabla x, " else "" in 
	let bodyOfTheTheorem = if (premisesTyp @ premisesSubSubstituted) = [] then "" else " -> " ^ existentialQuantification (List.map generateTerm varsLeftOvers) ^ nablaQuantification ^ generateANDformulaBetween (premisesTyp @ premisesSubSubstituted) in 
	let theorem = theoremPreamble ^ wrappedInBrackets (generateFormula typeFact) ^ bodyOfTheTheorem ^ ".\n\n" in 
	let preamble = "induction on 1. intros Main. Subtype1 : case Main. \n" in 
	let numberOfPremisesTyp = List.length premisesTyp in 	
	(* 
		We need to know how many premises the typing rule will release by IH, because the subtyping premises will go after those.
		So, we can seek the i-th subtyping premise with index (i-th + numberOfPremisesTyp)
	 *)
	let adjustmentsForHypothetical numberOfPremisesTyp n = 
(*		let n = if is_backed subtypingRule (nthMinusOne premisesSub n) then n else n + 1 in *)
		let position1 = string_of_int (n-1) in 
		let position2 = string_of_int (n+numberOfPremisesTyp) in 
		Seq([Tactic(Named("New" ^ position1, Apply(subsumption_in_contexts_NAME, ["Arg_1_" ^ position1]))) ; Tactic(Cut("Arg_2_" ^ position2 ,"New" ^ position1))])  in 
	let proofTypingRule = [Seq([Tactic(Search)])] in 
	let proofSubsumptionCase = [Seq([Tactic(Named("Arg_1_1", Apply(inversion_subtype_NAME ^ "_" ^ typOperator, ["Subtype2"]))) ; Tactic(Named("Arg_2_1", Apply("IH", ["Subtype1"])))] @ List.map (adjustmentsForHypothetical numberOfPremisesTyp) (findIndicesByPred formula_isHypothetical (premisesSub)) @ [Tactic(Search)])] in 
	 if (premisesTyp @ premisesSubSubstituted) = [] 
	 	then (greaterIneed, [], Theorem(theorem, Tactic(Search)))
	 	else (greaterIneed, premisesTyp @ premisesSubSubstituted, Theorem(theorem ^ preamble, Seq(proofTypingRule @ proofSubsumptionCase)))	
		 
	(* 
		Unusually, we do that inversion_typing returns a pair (list of premises, Theorem)  
		This is because other parts of the certifier needs those premises 
	*)
	
let inversion_error errorSpec = 
	let op = term_getOperator (specTerm_getSig errorSpec) in 	
	let typingRule = specTerm_getTyping errorSpec in 
	let conclusion = rule_getConclusion typingRule in 
	let premises = rule_getPremises typingRule in 
	let theoremPreamble = "Theorem " ^ inversion_typing_NAME ^ "_" ^ op ^ " : " ^ universalQuantification (List.map generateTerm (removeDuplicates (rule_getAllVariables typingRule))) in 
	let bodyOfTheTheorem = if premises = [] then "" else " -> " ^ generateANDformulaBetween premises in 	
	let theorem = theoremPreamble ^ wrappedInBrackets (generateFormula conclusion) ^ bodyOfTheTheorem ^ ".\n\n" in 
	let preamble = "induction on 1. intros Main. TypeOf1 : case Main. \n" in 
	let proofTypingRule = [Seq([Tactic(Search)])] in 
	let proofSubsumptionCase = [Seq([Tactic(Apply("IH", ["TypeOf1"])) ; Tactic(Search)])] in 
    if premises = [] 
	   then ([], Theorem(theorem, Tactic(Search)))
	   else (premises, Theorem(theorem ^ preamble, Seq(proofTypingRule @ proofSubsumptionCase)))		

let listCasesLemma ldl typeOperator  = 
	let c = (chop_last_char typeOperator 'T') in 
	let consDecl_virtual = DeclType(consListT c, [Simple(Inv,"") ; Simple(Inv,"") ; Simple(Inv,"")]) in  (* Simple here it is just to add an argument for the list *)
	let existentialForCons = type_existentiallyClosedEquation "List" consDecl_virtual in 
	let typedList = Formula(subtype, [Constructor(c ^ "T", [Var "List"]) ; Constructor(c ^ "T", [Var "List"])], []) in  
	let theorem = "Theorem " ^ memberCasesLemma (c ^ "T") ^ " : forall List, " 
		^ wrappedInBrackets (generateFormula typedList) ^ " -> "
		^ "List = " ^ generateTerm (Constructor(emptyListT c, [])) 
		^ " \\/ "
		^ type_existentiallyClosedEquation "List" consDecl_virtual 
		^ "."
		in 
		  	[Theorem(theorem ^ " skip.", Qed)]

let wrapped_inversion_subtype subtyping ldl (c, rule) = (* add one more "search." if the list has width subtyping because there is one more case  *)
	let (_, Theorem(thm,proof)) = inversion_subtype ldl (c, rule) in 
	let adjustedProof = if subtyping_isWidthSubtyping subtyping c then appendProof (Tactic(Search)) proof else proof in 
	  listCasesLemma ldl c @ [Theorem(thm,adjustedProof)]
	
	
let generateSubtypingLemmas ldl subtyping = if is_none subtyping then [] else 
	match ldl with SafeTypedLanguage(types, derived, errorSpec) -> 
		let typesThatHaveEliminators = List.filter (fun specType -> not (specType_getEliminators specType = [])) types in 
		let subtypingRulesForNoLists = subtyping_getRulesForNoLists ldl subtyping in 
		let subtypingRulesForLists = subtyping_getRulesForLists ldl subtyping in (* Notice that this return only the MAIN one subtyping rule, and not 2 rules for one type operator *)
		let constructorsThatHaveEliminators = List.concat (List.map specType_getConstructors typesThatHaveEliminators) in 
		let constructorsThatHaveEliminatorsAndAreNotLists = List.filter (fun termSpec -> not (termDecl_isList (specTerm_getSig termSpec))) constructorsThatHaveEliminators in 
			subsumption_in_contexts_lemma ::
			List.map snd (List.map (inversion_subtype ldl) subtypingRulesForNoLists)
			@ List.concat (List.map (wrapped_inversion_subtype subtyping ldl) subtypingRulesForLists)
			@ List.map get3_3 (List.map (inversion_typing subtypingRulesForNoLists) constructorsThatHaveEliminatorsAndAreNotLists) 
			@ if ldl_containErrors ldl then [snd (inversion_error (ldl_getErrorDeclaration ldl))] else []   
			

		