
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

let term_isConstructor term = match term with Constructor(c, args) -> true  | otherwise -> false
let term_isVar term = match term with Var(name) -> true | otherwise -> false
let term_isApplication term = match term with Application(term1,term2) -> true | otherwise -> false
let term_getConstructor term = match term with Constructor(c, args) -> c | otherwise -> raise(Failure ("term_getConstructor: " ^ toString term)) 
let term_getArguments term = match term with Constructor(c, args) -> args | otherwise -> raise(Failure ("term_getArguments: " ^ toString term))
let term_getNestedFirstArgument term = term_getConstructor (List.hd (term_getArguments term))
let type_getOperator typeDecl = match typeDecl with DeclType(c,arguments) -> c
let term_getOperator termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> c
let term_getValPositions termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> valpos
let term_getContextInfo termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> ctx
let term_getContextualPositions termDecl = List.map fst (term_getContextInfo termDecl)

let rec term_getVariables term = match term with 
| Var(name) -> [Var(name)]
| Constructor(name, arguments) -> List.concat (List.map term_getVariables arguments)
| Application(term1, term2) -> term_getVariables term1 @ term_getVariables term2

let term_getExpressionNumber termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> List.length (List.filter (fun entry -> entry_toKindProduced entry = termKind) arguments)
let term_getExpressionVariables termDecl term = List.take (term_getExpressionNumber termDecl) (term_getVariables term)
let term_disjointTerms args = args = removeDuplicates args
let term_isCanonicalRelaxedFor operatorname term = if term_isConstructor term then term_getConstructor term = operatorname && List.for_all term_isVar (term_getArguments term) else false
let term_isCanonicalFor operatorname term = term_isCanonicalRelaxedFor operatorname term && term_disjointTerms (term_getArguments term)

let rule_getConclusion rule = match rule with Rule(name, premises, conclusion) -> conclusion
let rule_getRuleName rule = match rule with Rule(name, premises, conclusion) -> name
let rule_getPremises rule = match rule with Rule(name, premises, conclusion) -> premises
let rule_getOutputTerm rule = match rule_getConclusion rule with Formula(pred, inputs, outputs) -> try List.hd outputs with Failure e -> raise(Failure ("rule_getOutputTerm: " ^ (rule_getRuleName rule)))
let rule_getInputTerm rule = match rule_getConclusion rule with Formula(pred, inputs, outputs) -> try List.hd inputs with Failure e -> raise(Failure ("rule_getInputTerm: " ^ (rule_getRuleName rule)))
let rule_getConstructorOfOutput rule = term_getConstructor (rule_getOutputTerm rule)
let rule_getConstructorOfInput rule = term_getConstructor (rule_getInputTerm rule)
let rule_addPremises newpremises rule = match rule with Rule(name, premises, conclusion) -> Rule(name, premises @ newpremises, conclusion)

let tl_getTypes tl = match tl with TypedLanguage(type_decls, term_decls, rules) -> type_decls
let tl_getTerms tl = match tl with TypedLanguage(type_decls, term_decls, rules) -> term_decls
let tl_getRules tl = match tl with TypedLanguage(type_decls, term_decls, rules) -> rules
let tl_setRules tl newrules = match tl with TypedLanguage(type_decls, term_decls, rules) -> TypedLanguage(type_decls, term_decls, newrules)
let tl_lookupTypeDecl tl c = let searchbyname typeDecl = type_getOperator typeDecl = c in try List.hd (List.filter searchbyname (tl_getTypes tl)) with Failure e -> raise(Failure ("tl_lookupTypeDecl: " ^ c))
let tl_lookupTermDecl tl c = let searchbyname termDecl = term_getOperator termDecl = c in try List.hd (List.filter searchbyname (tl_getTerms tl)) with Failure e -> raise(Failure ("tl_lookupTermDecl: " ^ c))
let tl_isEmpty tl = match tl with TypedLanguage(type_decls, term_decls, rules) -> rules = []

let formula_isHypothetical premise = match premise with 
	| Hypothetical(term1, term2, term3) -> true
	| otherwise -> false

let formula_getFirstInput premise = match premise with 
	| Formula(pred1, inputs, outputs) -> if inputs = [] then raise(Failure "formula_getFirstInput") else List.hd inputs
	| Hypothetical(term1, term2, term3) -> term2
	| Generic(term1, term2) -> term1

let formula_getHypotheticalPart premise = match premise with 
	| Hypothetical(term1, term2, term3) -> term1
	| _ -> raise(Failure "formula_getHypotheticalPart : the premise is not hypothetical")

let formula_getFirstInputUpToApp premise = let term = (formula_getFirstInput premise) in if term_isApplication term then match term with Application(term1, term2) -> term1 else term

let formula_getFirstOutput premise = match premise with 
	| Formula(pred1, inputs, outputs) -> if outputs = [] then raise(Failure "formula_getFirstOutput") else List.hd outputs
	| Hypothetical(term1, term2, term3) -> term3
	| Generic(term1, term2) -> term2
	
let formula_isPredicate pred1 premise = match premise with 
| Formula(pred2, inputs, outputs) -> pred1 = pred2
| otherwise -> pred1 = typing
let formula_isTyping premise = formula_isPredicate typing premise

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

let term_toPosition term (abs, applied) = 
	try 
	let retrieve var = (let index = List.index_of var (term_getArguments term) in if is_none index then (2, get (List.index_of var (term_getArguments (List.hd (term_getArguments term))))) else (1, get index)) in
	let coordinatesAbs = retrieve abs in 
	let ccordinatesApplied = if term_isVar applied then retrieve applied else (0, 0) in
	if term_isConstructor term then (coordinatesAbs, ccordinatesApplied, applied) else raise(Failure "term_toPosition : top level term is not a constructor.")
	with _ -> raise(Failure("term_toPosition :" ^ toString term))
	
let toValuePremise term = Formula("value", [term], [])

	(*
((1,1),(2,2), "asd") 	 no, applied can be of the toplevel or nested term, and you need to grab that typing rule. 
	Moreover the variable used in the reduction rule has nothing to do with the one in the typing rule 
	let typingrule = ... in 
*)