open Topo
open Batteries
open Option
open Aux

let typing = "typeOf"
let errorPred = "error"
let valuePred = "value"
let reduction = "step"
let typeKind = "typ"
let termKind = "term"
let equality = "equal"

type kindname= string
type typeoperator = string
type termoperator = string
type varname = string
type predicatename = string
type rulename = string

type term =
  | Var of varname
  | Constructor of typeoperator  * term list 
  | Application of term * term 
  | Bound of string 

type variance = Cov | Contra | Inv | Normal | Rec
type width = bool
type list_info = (variance * width)

type type_expression = 
  | Simple of variance  * kindname
  | Abstraction of variance  * (kindname  * kindname) 
  | List of list_info * typeoperator * term
  | ListSelf of list_info * typeoperator * term

type signature_type =
  | DeclType of typeoperator * type_expression list

type position = int
type position_of_values = (position list)
type contextual_entry = (position * position_of_values)
type ctx_info = contextual_entry list

type signature_term =
	| DeclTrm of termoperator * position_of_values * ctx_info * type_expression list

(* Example: Formula predicateName inputTerms outputTerms *)
type formula =
  | Formula of predicatename * term list * term list
  | Hypothetical of formula * formula
  | Generic of formula

type rule =
  | Rule of rulename * formula list * formula


type typed_language =
  | TypedLanguage of signature_type list * signature_term list * rule list 

  let rec toString term = match term with 
    | Var(name) -> name
    | Constructor(name, arguments) -> "(" ^ name ^ " " ^ String.concat " " (List.map toString arguments) ^ ")"
    | Application(term1, term2) -> "(" ^ toString term1 ^ " " ^ toString term2 ^ ")"
	| Bound(name) -> name
  let rec toStringWith' term = match term with 
    | Var(name) -> name ^ "'"
    | Constructor(name, arguments) -> name ^ " " ^ String.concat " " (List.map toStringWith' arguments)
  let toStringFromList vars = " " ^ (String.concat " " (List.map toString vars))
  let rec term_withTick index term = match term with 
  	| Var(name) -> Var(name ^ "'")
  	| Constructor(name, arguments) -> Constructor(name, List.take index arguments @ [term_withTick 0 (List.nth arguments index)] @ List.drop (index+1) arguments)


type subtyping_structure = 
	| Subtyping of (typeoperator option) * ((typeoperator * int) * variance) list * (typeoperator * rule) list 


let tl_extend (TypedLanguage(type_decls1, term_decls1, rules1)) (TypedLanguage(type_decls2, term_decls2, rules2)) = TypedLanguage(type_decls1 @ type_decls2, term_decls1 @ term_decls2, rules1 @ rules2)

let toVar varname = Var(varname)
let toTicked var = match var with | Var(varname) -> Var(var_ticked varname) | other -> raise(Failure("toTicked: " ^ (dump other)))

let rec term_AllwithTick term = match term with 
	| Var(name) -> Var(name ^ "'")
	| Constructor(name, arguments) -> Constructor(name, List.map toTicked arguments)
let entry_isAbstraction entry = match entry with Abstraction(variance,(kind1, kind2)) -> true | otherwise -> false
let entry_toKindProduced entry = match entry with Simple(variance, kind) -> kind | Abstraction(variance,(kind1, kind2)) -> kind2 | List(_) -> "list" | ListSelf(_) -> "list"
let ctx_isAcyclic ctx = try (let order = topo_compute_order ctx in true) with _ -> false

let kind_isAuxiliary entry = not ( entry_toKindProduced entry == typeKind || entry_toKindProduced entry == termKind)

let term_isConstructor term = match term with Constructor(c, args) -> true  | otherwise -> false
let term_isVar term = match term with Var(name) -> true | otherwise -> false
let term_isApplication term = match term with Application(term1,term2) -> true | otherwise -> false
let term_getConstructor term = match term with Constructor(c, args) -> c | otherwise -> raise(Failure ("term_getConstructor: " ^ toString term)) 
let term_getArguments term = match term with Constructor(c, args) -> args | otherwise -> raise(Failure ("term_getArguments: " ^ toString term))
let term_getNestedFirstArgument term = (List.hd (term_getArguments term))
let term_getNestedFirstArgumentConstructor term = term_getConstructor (term_getNestedFirstArgument term)
let type_getOperator typeDecl = match typeDecl with DeclType(c,arguments) -> c
let type_getArguments typeDecl = match typeDecl with DeclType(c,arguments) -> arguments
let term_getOperator termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> c
let termDecl_getArguments termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> arguments
let term_getValPositions termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> valpos
let term_getContextInfo termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> ctx
let term_setContextInfo termDecl ctx = match termDecl with DeclTrm(c, valpos, _, arguments) -> DeclTrm(c, valpos, ctx, arguments)
let term_getContextualPositions termDecl = List.map fst (term_getContextInfo termDecl)
let term_isBound term = term = Var("x") (* Needed in preservation. This should be done better *)

let type_getListVariance typeDecl = match typeDecl with 
	| DeclType(c,[(List((variance,width), c2, trm))]) -> variance
	| DeclType(c,[(ListSelf((variance,width), c2, trm))]) -> variance

let termDecl_insertCtx ctxlines termDecl = match termDecl with DeclTrm(c, _, _, arguments) ->
	let ctxlinesOnlyThoseOfc = List.map snd (List.filter (fun pair -> fst pair = c) ctxlines) in 
	let linesInNumbers = List.map (fun line -> List.mapi (fun i -> fun letter -> match letter with | "v" -> i+1 | "C" -> 0 | otherwise -> -1) line) ctxlinesOnlyThoseOfc in 
	let contextualPositions = List.map (fun line -> 1 + get (List.index_of 0 line)) linesInNumbers in 
	let valuehoodPositions = List.map (fun line -> List.filter (fun n -> n > 0) line) linesInNumbers in 
	let contexts = List.combine contextualPositions valuehoodPositions in 
	 DeclTrm(c, [], contexts, arguments)

	 (* Here we have value = [n] where n = 1 means ALL, n = 2 means First, n = 3 means NONE
	    and ctx-info = [ (1, [n]) ] where n = 1 means SEQ, n = 2 means Parallel *)
let termDecl_insertListInfo listinfo varianceInfo termDecl = match termDecl with | DeclTrm(c, valpos, ctx, arguments) ->
	let retrieve_ c1 ((c2,n), tag) = if c1 = (chop_last_char c2 'T') then Some tag else None in
	let retrieve c varianceInfo = List.map get (List.filter is_some (List.map (retrieve_ c) varianceInfo)) in 
	let newArgs = (match arguments with 
		| [(List((variance,width), c2, trm))] -> (try (let tag = List.hd (retrieve c2 varianceInfo) in [(List((tag,width), c2, trm))]) with _ -> arguments)
		| [(ListSelf((variance,width), c2, trm))] -> (try (let tag = List.hd (retrieve c2 varianceInfo) in [(ListSelf((tag,width), c2, trm))]) with _ -> arguments)
		| _ -> arguments) in 
	let newTrm = DeclTrm(c, valpos, ctx, newArgs) in 
	let insert info = DeclTrm(c, [fst info], [(snd info, [])], newArgs) in 
	(try (insert (List.assoc c listinfo)) with Not_found -> newTrm)

	

let rec term_getVariables term = match term with 
| Var(name) as tt -> if term_isBound tt then [] else [Var(name)]
| Constructor(name, arguments) -> List.concat (List.map term_getVariables arguments)
| Application(term1, term2) -> term_getVariables term1 @ term_getVariables term2
| Bound(name) as tt -> []

let term_getExpressionVariables termDecl term = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> 
	let nullNonPrograms i entry = if entry_toKindProduced entry = termKind then List.nth (term_getVariables term) i else Var("0") in 
	let stripNulls var = not(var = Var("0")) in
		List.filter stripNulls (List.mapi nullNonPrograms arguments)

let term_digIfApplication term = if term_isApplication term then match term with Application(term1, term2) -> term1 else term 
let vars_disjoint vars = vars = removeDuplicates vars
let term_isSkeletonFor operatorname term = if term_isConstructor term then term_getConstructor term = operatorname && List.for_all term_isVar (term_getArguments term) && vars_disjoint (term_getVariables term) else false
let term_isSkeletonMayNestFor operatorname term = 	term_isSkeletonFor operatorname term || 
													if term_getArguments term = [] then false else let nested = List.hd (term_getArguments term) in if term_isConstructor nested then term_isSkeletonFor (term_getNestedFirstArgumentConstructor term) nested else false 
let rule_getConclusion rule = match rule with Rule(name, premises, conclusion) -> conclusion
let rule_getRuleName rule = match rule with Rule(name, premises, conclusion) -> name
let rule_getPremises rule = match rule with Rule(name, premises, conclusion) -> premises
let rule_getOutputTerm rule = match rule_getConclusion rule with Formula(pred, inputs, outputs) -> try List.hd outputs with Failure e -> raise(Failure ("rule_getOutputTerm: " ^ (dump rule)))
let rule_getInputTerm rule = match rule_getConclusion rule with Formula(pred, inputs, outputs) -> try List.hd inputs with Failure e -> raise(Failure ("rule_getInputTerm: " ^ (dump rule)))
let rule_getConstructorOfOutput rule = term_getConstructor (rule_getOutputTerm rule)
let rule_getConstructorOfInput rule = term_getConstructor (rule_getInputTerm rule)
let rule_addPremises newpremises rule = match rule with Rule(name, premises, conclusion) -> Rule(name, premises @ newpremises, conclusion)

let rule_checkEliminatesSome rule = 
	if term_isConstructor (rule_getInputTerm rule) then 
		let args = term_getArguments (rule_getInputTerm rule) in
		if args = [] then false else term_isConstructor (List.hd args) 
	else false

let rule_checkEliminatesWhat rule = 
		let args = term_getArguments (rule_getInputTerm rule) in term_getConstructor (List.hd args) 
	
let tl_getTypes tl = match tl with TypedLanguage(type_decls, term_decls, rules) -> type_decls
let tl_getTerms tl = match tl with TypedLanguage(type_decls, term_decls, rules) -> term_decls
let tl_getRules tl = match tl with TypedLanguage(type_decls, term_decls, rules) -> rules
let tl_setRules tl newrules = match tl with TypedLanguage(type_decls, term_decls, rules) -> TypedLanguage(type_decls, term_decls, newrules)
let tl_lookupTypeDecl tl c = let searchbyname typeDecl = type_getOperator typeDecl = c in try List.hd (List.filter searchbyname (tl_getTypes tl)) with Failure e -> raise(Failure ("tl_lookupTypeDecl: " ^ c))
let tl_lookupTermDecl tl c = let searchbyname termDecl = term_getOperator termDecl = c in try List.hd (List.filter searchbyname (tl_getTerms tl)) with Failure e -> raise(Failure ("tl_lookupTermDecl: " ^ c))
let tl_isEmpty tl = match tl with TypedLanguage(type_decls, term_decls, rules) -> rules = []
let tl_addRules tl newrules = match tl with TypedLanguage(type_decls, term_decls, rules) -> TypedLanguage(type_decls, term_decls, rules @ newrules)
let tl_removeRules tl oldrules = match tl with TypedLanguage(type_decls, term_decls, rules) -> TypedLanguage(type_decls, term_decls, list_difference rules oldrules)

let term_decls_lookup tl c =
	let onlyByC term = term_getOperator term = c in 
	List.hd (List.filter onlyByC (tl_getTerms tl))

let types_decls_lookup tl c =
	let onlyByC term = type_getOperator term = c in 
	List.hd (List.filter onlyByC (tl_getTypes tl))

let formula_isHypothetical premise = match premise with 
	| Hypothetical(formula1, formula2) -> true
	| otherwise -> false

let formula_isGeneric premise = match premise with 
	| Generic(formula) -> true
	| otherwise -> false

let formula_isWithContext premise = formula_isHypothetical premise || formula_isGeneric premise

let rec formula_getPredicate premise = match premise with 
| Formula(pred, inputs, outputs) -> pred
| Hypothetical(formula1, formula2) -> formula_getPredicate formula2
| Generic(formula) -> formula_getPredicate formula

let rec formula_getInputs premise = match premise with 
	| Formula(pred1, inputs, outputs) -> inputs
	| Hypothetical(formula1, formula2) -> formula_getInputs formula2
	| Generic(formula) -> formula_getInputs formula

let rec formula_getOutputs premise = match premise with 
	| Formula(pred1, inputs, outputs) -> outputs
	| Hypothetical(formula1, formula2) -> formula_getOutputs formula2
	| Generic(formula) -> formula_getOutputs formula

let formula_getLastArgument premise = List.last (formula_getInputs premise @ formula_getOutputs premise)

let rec formula_getFirstInput premise = match premise with 
	| Formula(pred1, inputs, outputs) -> if inputs = [] then raise(Failure "formula_getFirstInput") else List.hd inputs
	| Hypothetical(formula1, formula2) -> formula_getFirstInput formula2
	| Generic(formula) -> formula_getFirstInput formula

let rec formula_getFirstOutput premise = match premise with 
	| Formula(pred1, inputs, outputs) -> if outputs = [] then raise(Failure "formula_getFirstOutput") else List.hd outputs
	| Hypothetical(formula1, formula2) -> formula_getFirstOutput formula2
	| Generic(formula) -> formula_getFirstOutput formula

let formula_getHypotheticalOutput premise = match premise with 
	| Hypothetical(formula1, formula2) -> formula_getFirstOutput formula1
	| _ -> raise(Failure "formula_getHypotheticalPart : the premise is not hypothetical")

let formula_getHypotheticalPart premise = match premise with 
	| Hypothetical(formula1, formula2) -> formula1
	| _ -> raise(Failure "formula_getHypotheticalPart : the premise is not hypothetical")
	
let formula_getHypotheticalPredicate premise = match premise with 
	| Hypothetical(formula1, formula2) -> formula_getPredicate formula1
	| _ -> raise(Failure "formula_getHypotheticalPart : the premise is not hypothetical")


let formula_putInInput formula term = match formula with Formula(pred, inputs, outputs) -> Formula(pred, term :: (List.tl inputs), outputs)

let formula_getFirstInputUpToApp premise = let term = (formula_getFirstInput premise) in if term_isApplication term then match term with Application(term1, term2) -> term1 else term
let formula_getFirstOutputUpToApp premise = let term = (formula_getFirstOutput premise) in if term_isApplication term then match term with Application(term1, term2) -> term1 else term

let formula_getAllOutputVars formula = term_getVariables (formula_getFirstOutput formula)
let premises_getAllOutputVars premises = List.concat (List.map formula_getAllOutputVars premises)
	
let formula_isPredicate pred premise = formula_getPredicate premise = pred

let formula_isTyping premise = formula_isPredicate typing premise

let formula_getRuleNameFromConclusion formula = match formula with Formula(pred, inputs, outputs) -> 
	if pred = reduction then let preName = "r_" ^ (term_getConstructor (List.hd inputs)) in
		 if rule_checkEliminatesSome (Rule("", [], formula)) then preName ^ "_" ^ term_getConstructor (List.hd (term_getArguments (List.hd inputs))) else preName
	else if pred = typing then "t_" ^ (term_getConstructor (List.hd inputs))
	else pred

let formula_turnToUnaryPredicate newPred formula = match formula with Formula(pred, inputs, outputs) -> Formula(newPred, inputs, [])
let formula_freeOutput formula = match formula with Formula(pred, inputs, outputs) -> Formula(pred, inputs, [Var "T"])
let term_isFreeVar rule term = term_isVar term && not(List.mem term (term_getVariables (rule_getInputTerm rule) @ List.concat (List.map term_getVariables (List.map formula_getFirstOutput (rule_getPremises rule)))))

let rec formula_getAllVariables premise = match premise with 
	| Formula(pred1, inputs, outputs) -> List.concat (List.map term_getVariables inputs) @ List.concat (List.map term_getVariables outputs)
	| Hypothetical(formula1, formula2) -> formula_getAllVariables formula1 @ formula_getAllVariables formula2 
	| Generic(formula) -> formula_getAllVariables formula

let rule_getAllVariables rule = List.concat (List.map formula_getAllVariables (rule_getPremises rule)) @ formula_getAllVariables (rule_getConclusion rule)
let rule_isPredicate pred rule = formula_isPredicate pred (rule_getConclusion rule)
let rule_isTypingRule rule = rule_isPredicate typing rule
let rule_isReductionRule rule = rule_isPredicate reduction rule
let rule_isPredicateAndName pred c rule = formula_isPredicate pred (rule_getConclusion rule) && rule_getConstructorOfInput rule = c
let rule_turnFormulaTo pred formula = match formula with Formula(_, inputs, outputs) -> Formula(pred, inputs, outputs)
let rule_addOutputFromTypingRule typingRule formula = match formula with Formula(pred, inputs, outputs) -> Formula(pred, inputs, [rule_getOutputTerm typingRule])
let rule_outputBecomesInput formula = match formula with Formula(pred, inputs, outputs) -> Formula(pred, outputs, [])
let rule_getNestedOperatorInEliminationRule rule = term_getNestedFirstArgumentConstructor (rule_getInputTerm rule)
let rule_getNestedTermInEliminationRule rule = term_getNestedFirstArgument (rule_getInputTerm rule)
let rec term_retrieveApplications term = match term with 
| Var(name) -> []
| Constructor(name, arguments) -> List.concat (List.map term_retrieveApplications arguments)
| Application(term1, term2) -> if term_isVar term1 then [(term1, term2)] else raise(Failure ("term_retrieveApplications: error in Application(term1, term2), term1 is not a variable"))
let rule_replaceInput (Rule(name, premises, (Formula(pred1, inputs, outputs)))) term = (Rule(name, premises, (Formula(pred1, term :: (List.tl inputs), outputs))))
(* adjustIndex takes the index of an argument, and subtract the number of arguments before that that are not programs. 
   For example, in (abs T R), R comes with index 2, but here we adjust to return 1, as it is the first program variable. 
   This index points to the first hypothesis in the proof of preservation, because hypothesis exists only for program arguments. 
	*)
let adjustIndex tl c index = let turnToZeroOnes i entry = if i < 4 && not(entry_toKindProduced entry = "term") then 1 else 0 in index - (List.fold_left (+) 0 (List.mapi turnToZeroOnes (termDecl_getArguments (term_decls_lookup tl c))))

let application_getApplied term = match term with Application(term1,term2) -> term2

let term_toPosition tl term (abs, applied) = 
	try 
	let retrieve var = (let index = List.index_of var (term_getArguments term) in 
		if is_none index 
			then let nestedTerm = List.hd (term_getArguments term) in 
				 let kindOfArguments = (termDecl_getArguments (term_decls_lookup tl (term_getConstructor nestedTerm))) in 
				 	(2, get (List.index_of var (term_getArguments nestedTerm)), kindOfArguments) 
			else let kindOfArguments = (termDecl_getArguments (term_decls_lookup tl (term_getConstructor term))) in 
				(1, get index, kindOfArguments)) in
	let coordinatesAbs = retrieve abs in 
	let ccordinatesApplied = if term_isVar applied then retrieve applied else (0, 0, []) in (* if we apply a var we can find its hypothesis by position. Otherwise the tool simply generate an 'assert typeOf ..' *)
	if term_isConstructor term then (coordinatesAbs, ccordinatesApplied, applied) else raise(Failure "term_toPosition : top level term is not a constructor.")
	with _ -> raise(Failure("term_toPosition :" ^ toString term))

(* Index managements *)
let index_fst (a,b,c) = a
let index_snd (a,index,arguments) = let turnToZeroOnes i entry = if i < index && not(entry_toKindProduced entry = "term") then 1 else 0 in index - (List.fold_left (+) 0 (List.mapi turnToZeroOnes arguments))
let index_sndReal (a,b,c) = b
		
let toValuePremise term = Formula("value", [term], [])
let toErrorPremise term = Formula("error", [term], [])
	(*
((1,1),(2,2), "asd") 	 no, applied can be of the toplevel or nested term, and you need to grab that typing rule. 
	Moreover the variable used in the reduction rule has nothing to do with the one in the typing rule 
	let typingrule = ... in 
*)
		

(* returns the operator and the position checked. so (c, [1,2 ..])*) 
(* notice that it is ok for a variable to be checked for valuehood in a premise and NOT being part of the operator checked. 
	example: step (unfold (fold V R)) V :- value V. V is in fold and not unfold, we do not return a position for that. i.e. return 0 and drop it.
	
	 *)
let positionsCheckedForValuehood rule = 
	let mentionedArgument term premise = (match (List.index_of (formula_getFirstInput premise) (term_getArguments term)) with 
		| None -> 0
		| Some i -> 1 + i)
	in (rule_getConstructorOfInput rule, List.filter (fun x -> x > 0) (List.map (mentionedArgument (rule_getInputTerm rule)) (rule_getPremises rule))) 
	
let typecheckSubtyping subtypingRule = 
	if rule_getRuleName subtypingRule = "record_width" then subtypingRule else 
	let checkSubtypingPremises (t1,t2) = List.exists (fun premise -> formula_getPredicate premise = "subtype" 
																&& (  list_subset [t1 ; t2] (List.map term_digIfApplication ((formula_getInputs premise) @ (formula_getOutputs premise)))
																				||
																				t1 = t2
																	)
													  )
													  (rule_getPremises subtypingRule) in 
	match rule_getConclusion subtypingRule with 
		| Formula(pred, inputs, outputs) -> match inputs @ outputs  with 
			| [Constructor(c1, args1) ; Constructor(c2, args2)] -> 
				if c1 = c2 
					then 
									if List.for_all checkSubtypingPremises (List.combine args1 args2) 
									then subtypingRule  
									else raise(Failure("Subtyping rule does not recursively compare types in the right form: " ^ (rule_getRuleName subtypingRule)))
					else raise(Failure("This subtyping rule does not compare the same type: " ^ (rule_getRuleName subtypingRule)))
			| _ -> raise(Failure("This subtyping rule is not in the right form: " ^ (rule_getRuleName subtypingRule)))
		| _ -> raise(Failure("This subtyping rule is not in the right form: " ^ (rule_getRuleName subtypingRule)))
	
let create_subtyping upTo top varianceList specialRules = 
	if not(upTo) 
		then None 
		else let check = List.map typecheckSubtyping (List.map snd specialRules) in 
			Some (Subtyping(top, varianceList, specialRules)) 

let subtyping_getTop (Some (Subtyping(top, varianceList, rules))) = top
let subtyping_getVariance (Some (Subtyping(top, varianceList, rules))) = varianceList
let subtyping_getRules (Some (Subtyping(top, varianceList, rules))) = rules

let rec term_substitutions associations term = match term with
         | Var(variable) ->
			 (try (List.assoc (Var(variable)) associations) with Not_found -> 
			 	(try (List.assoc (Bound(variable)) associations) with Not_found -> (Var(variable))))
         | Application(term1,term2) -> Application(term_substitutions associations term1, term_substitutions associations term2)
         | Constructor(c,args) -> Constructor(c,List.map (term_substitutions associations) args)
         | Bound(variable) -> 
			 (try (List.assoc (Var(variable)) associations) with Not_found -> 
			 	(try (List.assoc (Bound(variable)) associations) with Not_found -> (Bound(variable))))
			 
let rec formula_substitutions associations premise = match premise with 
	| Formula(pred1, inputs, outputs) -> Formula(pred1, List.map (term_substitutions associations) inputs, List.map (term_substitutions associations) outputs) 
	| Hypothetical(formula1, formula2) -> Hypothetical(formula_substitutions associations formula1, formula_substitutions associations formula2)
	| Generic(formula) -> Generic(formula_substitutions associations formula)


let conclusion_implicitValuePremises formula = 
	let scanForVs (Var varname) = String.starts_with varname "V" in 
	if formula_isPredicate "step" formula || formula_isPredicate "value" formula then List.map toValuePremise (List.filter scanForVs (formula_getAllVariables formula)) else []
	
	
let rule_substitutions associations (Rule(name, premises, conclusion)) = Rule(name, List.map (formula_substitutions associations) premises, formula_substitutions associations conclusion)

let rule_lookup_premise_by_var (Rule(name, premises, conclusion)) var = 
	let spotPremise i premise = if formula_getFirstInputUpToApp premise = var then i+1 else -1 in 
	  let answer = List.filter (fun i -> i>0) (List.mapi spotPremise premises) in 
	   if answer = [] then None else Some (List.hd answer)


let substitution_avoid_capture premises associations = 
	let varsInPremises = removeDuplicates (List.concat (List.map formula_getAllVariables premises)) in 
	let varsTarget = removeDuplicates (List.map snd associations) in 
	let variablesInCommon = list_difference varsInPremises (list_difference varsInPremises varsTarget) in 
	let avoids = List.combine variablesInCommon (List.map toTicked variablesInCommon) in 
	 List.map (formula_substitutions avoids) premises

let toEqual (term1,term2) = (Formula(equality, [term1 ; term2], []))
let fromEqualityToSubstitution (Formula(pred, [term1 ; term2], [])) = if pred = equality then (term1,term2) else raise(Failure("fromEqualityToSubstitution: given a formula that is not an equaloty"))

let term_getFormalVarByType arguments preIndex typeEntry = let index = preIndex + 1 in match typeEntry with 
  | Simple(variance, "term") -> Var("E" ^ (string_of_int index))
  | Abstraction(variance, (typ1, "term")) -> Var("R" ^ (string_of_int index))
  | Abstraction(variance, (typ1, "typ")) -> Var("U" ^ (string_of_int index))
  | Simple(variance, "typ") -> Var("T" ^ (string_of_int index))
  | Simple(variance, _) -> Var("L")
  | List(_) -> Var("List")
  | ListSelf(_) -> Var("List")

let term_getFormalVar index typeEntry = Var("Arg" ^ (string_of_int (index+1)))

let type_getCanonical typeDecl = match typeDecl with DeclType(c, arguments) -> let newVars = List.mapi (term_getFormalVarByType arguments) arguments in (Constructor(c,newVars), newVars)
(* below, type_getCanonical2 is equal to type_getCanonical, but it uses other letters for variables or it would clash *)
let term_getCanonical termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> let newVars = List.mapi (term_getFormalVarByType arguments) arguments in (Constructor(c,newVars), newVars)
let type_getCanonicalNoClash typeDecl = match typeDecl with DeclType(c, arguments) -> let newVars = List.mapi term_getFormalVar arguments in (Constructor(c,newVars), newVars)
let term_getCanonicalNoClash termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> let newVars = List.mapi term_getFormalVar arguments in (Constructor(c,newVars), newVars)

(* this is called in the context of subtyping where subtyping rules are in an assoc list (c,rule) *)
let substitute_equalities (c, (Rule(name, premises, conclusion))) = 
	let toAssocList formula = (let [inn ; out] = formula_getInputs formula in (out, inn)) in 
	let equalities = (List.filter (formula_isPredicate equality) premises) in 
	let associations = List.map toAssocList equalities in 
	(c, rule_substitutions associations (Rule(name, list_difference premises equalities, conclusion)))

