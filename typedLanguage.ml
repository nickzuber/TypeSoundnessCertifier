open Topo
open Batteries
open Option
open Aux

let typing = "typeOf"
let errorPred = "error"
let valuePred = "value"
let reduction = "step"
let termKind = "term"

type typename = string
type typeoperator = string
type termoperator = string
type varname = string
type predicatename = string
type rulename= string

type type_expression = 
  | Simple of typename
  | Abstraction of typename  * typename 

type signature_type =
  | DeclType of typeoperator * type_expression list

type position = int
type position_of_values = (position list)
type contextual_entry = (position * position_of_values)
type ctx_info = contextual_entry list

type signature_term =
	| DeclTrm of termoperator * position_of_values * ctx_info * type_expression list

type term =
  | Var of varname
  | Constructor of typeoperator  * term list 
  | Application of term * term 

(* Example: Formula predicateName inputTerms outputTerms *)
type formula =
  | Formula of predicatename * term list * term list
  | Hypothetical of term * term * term
  | Generic of term * term

type rule =
  | Rule of rulename * formula list * formula


type typed_language =
  | TypedLanguage of signature_type list * signature_term list * rule list 

  let rec toString term = match term with 
    | Var(name) -> name
    | Constructor(name, arguments) -> "(" ^ name ^ " " ^ String.concat " " (List.map toString arguments) ^ ")"
    | Application(term1, term2) -> "(" ^ toString term1 ^ " " ^ toString term2 ^ ")"
  let rec toStringWith' term = match term with 
    | Var(name) -> name ^ "'"
    | Constructor(name, arguments) -> name ^ " " ^ String.concat " " (List.map toStringWith' arguments)
  let toStringFromList vars = " " ^ (String.concat " " (List.map toString vars))
  let rec term_withTick index term = match term with 
  	| Var(name) -> Var(name ^ "'")
  	| Constructor(name, arguments) -> Constructor(name, List.take index arguments @ [term_withTick 0 (List.nth arguments index)] @ List.drop (index+1) arguments)

let toVar varname = Var(varname)

let entry_toKindProduced entry = match entry with Simple(kind) -> kind | Abstraction(kind1, kind2) -> kind2
let ctx_isAcyclic ctx = try (let order = topo_compute_order ctx in true) with _ -> false
(*
	let monotonicityAtEveryEntry pair = match pair with (index, indexes) -> List.for_all (fun x -> index > x) indexes  in 
	List.for_all monotonicityAtEveryEntry ctx   to do 
*)
let term_isConstructor term = match term with Constructor(c, args) -> true  | otherwise -> false
let term_isVar term = match term with Var(name) -> true | otherwise -> false
let term_isApplication term = match term with Application(term1,term2) -> true | otherwise -> false
let term_getConstructor term = match term with Constructor(c, args) -> c | otherwise -> raise(Failure ("term_getConstructor: " ^ toString term)) 
let term_getArguments term = match term with Constructor(c, args) -> args | otherwise -> raise(Failure ("term_getArguments: " ^ toString term))
let term_getNestedFirstArgument term = term_getConstructor (List.hd (term_getArguments term))
let type_getOperator typeDecl = match typeDecl with DeclType(c,arguments) -> c
let type_getArguments typeDecl = match typeDecl with DeclType(c,arguments) -> arguments
let term_getOperator termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> c
let termDecl_getArguments termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> arguments
let term_getValPositions termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> valpos
let term_getContextInfo termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> ctx
let term_getContextualPositions termDecl = List.map fst (term_getContextInfo termDecl)
let term_isBound term = term = Var("x") (* Needed in preservation. This should be done better *)

let termDecl_insertCtx ctxlines termDecl = match termDecl with DeclTrm(c, _, _, arguments) ->
	let ctxlinesOnlyThoseOfc = List.map snd (List.filter (fun pair -> fst pair = c) ctxlines) in 
	let linesInNumbers = List.map (fun line -> List.mapi (fun i -> fun letter -> match letter with | "v" -> i+1 | "E" -> 0 | otherwise -> -1) line) ctxlinesOnlyThoseOfc in 
	let contextualPositions = List.map (fun line -> 1 + get (List.index_of 0 line)) linesInNumbers in 
	let valuehoodPositions = List.map (fun line -> List.filter (fun n -> n > 0) line) linesInNumbers in 
	let contexts = List.combine contextualPositions valuehoodPositions in 
	 DeclTrm(c, [], contexts, arguments)
	 

let rec term_getVariables term = match term with 
| Var(name) as tt -> if term_isBound tt then [] else [Var(name)]
| Constructor(name, arguments) -> List.concat (List.map term_getVariables arguments)
| Application(term1, term2) -> term_getVariables term1 @ term_getVariables term2

let term_getExpressionVariables termDecl term = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> 
	let nullNonPrograms i entry = if entry_toKindProduced entry = termKind then List.nth (term_getVariables term) i else Var("0") in 
	let stripNulls var = not(var = Var("0")) in
		List.filter stripNulls (List.mapi nullNonPrograms arguments)

let vars_disjoint vars = vars = removeDuplicates vars
let term_isSkeletonFor operatorname term = if term_isConstructor term then term_getConstructor term = operatorname && List.for_all term_isVar (term_getArguments term) && vars_disjoint (term_getVariables term) else false
let term_isSkeletonMayNestFor operatorname term = 	term_isSkeletonFor operatorname term || 
													if term_getArguments term = [] then false else let nested = List.hd (term_getArguments term) in if term_isConstructor nested then term_isSkeletonFor (term_getNestedFirstArgument term) nested else false 
let rule_getConclusion rule = match rule with Rule(name, premises, conclusion) -> conclusion
let rule_getRuleName rule = match rule with Rule(name, premises, conclusion) -> name
let rule_getPremises rule = match rule with Rule(name, premises, conclusion) -> premises
let rule_getOutputTerm rule = match rule_getConclusion rule with Formula(pred, inputs, outputs) -> try List.hd outputs with Failure e -> raise(Failure ("rule_getOutputTerm: " ^ (rule_getRuleName rule)))
let rule_getInputTerm rule = match rule_getConclusion rule with Formula(pred, inputs, outputs) -> try List.hd inputs with Failure e -> raise(Failure ("rule_getInputTerm: " ^ (rule_getRuleName rule)))
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

let term_decls_lookup tl c =
	let onlyByC term = term_getOperator term = c in 
	List.hd (List.filter onlyByC (tl_getTerms tl))

let types_decls_lookup tl c =
	let onlyByC term = type_getOperator term = c in 
	List.hd (List.filter onlyByC (tl_getTypes tl))

let formula_isHypothetical premise = match premise with 
	| Hypothetical(term1, term2, term3) -> true
	| otherwise -> false

let formula_getFirstInput premise = match premise with 
	| Formula(pred1, inputs, outputs) -> if inputs = [] then raise(Failure "formula_getFirstInput") else List.hd inputs
	| Hypothetical(term1, term2, term3) -> term2
	| Generic(term1, term2) -> term1

let formula_getFirstOutput premise = match premise with 
	| Formula(pred1, inputs, outputs) -> if outputs = [] then raise(Failure "formula_getFirstOutput") else List.hd outputs
	| Hypothetical(term1, term2, term3) -> term3
	| Generic(term1, term2) -> term2

let formula_getHypotheticalPart premise = match premise with 
	| Hypothetical(term1, term2, term3) -> term1
	| _ -> raise(Failure "formula_getHypotheticalPart : the premise is not hypothetical")

let formula_getFirstInputUpToApp premise = let term = (formula_getFirstInput premise) in if term_isApplication term then match term with Application(term1, term2) -> term1 else term
let formula_getFirstOutputUpToApp premise = let term = (formula_getFirstOutput premise) in if term_isApplication term then match term with Application(term1, term2) -> term1 else term

	
let formula_isPredicate pred1 premise = match premise with 
| Formula(pred2, inputs, outputs) -> pred1 = pred2
| otherwise -> pred1 = typing
let formula_isTyping premise = formula_isPredicate typing premise

let formula_getRuleNameFromConclusion formula = match formula with Formula(pred, inputs, outputs) -> 
	if pred = reduction then let preName = "r_" ^ (term_getConstructor (List.hd inputs)) in
		 if rule_checkEliminatesSome (Rule("", [], formula)) then preName ^ "_" ^ term_getConstructor (List.hd (term_getArguments (List.hd inputs))) else preName
	else if pred = typing then "t_" ^ (term_getConstructor (List.hd inputs))
	else pred

let term_isFreeVar rule term = term_isVar term && not(List.mem term (term_getVariables (rule_getInputTerm rule) @ List.concat (List.map term_getVariables (List.map formula_getFirstOutput (rule_getPremises rule)))))

let formula_getAllVariables premise = match premise with 
	| Formula(pred1, inputs, outputs) -> List.concat (List.map term_getVariables inputs) @ List.concat (List.map term_getVariables outputs)
	| Hypothetical(term1, term2, term3) -> term_getVariables term1 @ term_getVariables term2 @ term_getVariables term3 
	| Generic(term1, term2) -> term_getVariables term1 @ term_getVariables term2

let rule_getAllVariables rule = List.concat (List.map formula_getAllVariables (rule_getPremises rule)) @ formula_getAllVariables (rule_getConclusion rule)
let rule_isPredicate pred rule = formula_isPredicate pred (rule_getConclusion rule)
let rule_isTypingRule rule = rule_isPredicate typing rule
let rule_isReductionRule rule = rule_isPredicate reduction rule
let rule_isPredicateAndName pred c rule = formula_isPredicate pred (rule_getConclusion rule) && rule_getConstructorOfInput rule = c
let rule_turnFormulaTo pred formula = match formula with Formula(_, inputs, outputs) -> Formula(pred, inputs, outputs)
let rule_addOutputFromTypingRule typingRule formula = match formula with Formula(pred, inputs, outputs) -> Formula(pred, inputs, [rule_getOutputTerm typingRule])
let rule_outputBecomesInput formula = match formula with Formula(pred, inputs, outputs) -> Formula(pred, outputs, [])
let rec term_retrieveApplications term = match term with 
| Var(name) -> []
| Constructor(name, arguments) -> List.concat (List.map term_retrieveApplications arguments)
| Application(term1, term2) -> if term_isVar term1 then [(term1, term2)] else raise(Failure ("term_retrieveApplications: error in Application(term1, term2), term1 is not a variable"))

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
		
		