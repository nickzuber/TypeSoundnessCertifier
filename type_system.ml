
open Batteries
open Aux

let typing = "typeOf"

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

type operator_info = 
| Constr of typename  
| Destr of typename 
| Derived of (typename option) 
| ErrorHandler
| Error 

type position_of_values = (int list)
type contextual_entry = (int * position_of_values)
type ctx_info = Contextual of contextual_entry list

type signature_term =
  | DeclTrm of termoperator * operator_info * ctx_info * type_expression list

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

(* Example: TypeSystem signatureForTypes signatureForTerms rules *)
type type_system =
  | TypeSystem of signature_type list * signature_term list * rule list 

let extend ts newrules = match ts with TypeSystem(signatureTypes, signatureTerms, rules) -> TypeSystem(signatureTypes, signatureTerms, List.append rules newrules)  

let rec toString term = match term with 
  | Var(name) -> name
  | Constructor(name, arguments) -> "(" ^ name ^ " " ^ String.concat " " (List.map toString arguments) ^ ")"
  | Application(term1, term2) -> "(" ^ toString term1 ^ " " ^ toString term2 ^ ")"

let rec toStringWith' term = match term with 
  | Var(name) -> name ^ "'"
  | Constructor(name, arguments) -> name ^ " " ^ String.concat " " (List.map toStringWith' arguments)

let toVar varname = Var(varname)

let term_getFormalVarByType arguments preIndex typeEntry = let index = preIndex + 1 in match typeEntry with 
  | Simple("term") -> Var("E" ^ (string_of_int index))
  | Abstraction(typ1, "term") -> Var("R" ^ (string_of_int index))
  | Abstraction(typ1, "typ") -> Var("U" ^ (string_of_int index))
  | Simple("typ") -> Var("T" ^ (string_of_int index))

let term_getFormalVar index typeEntry = Var("Arg" ^ (string_of_int (index+1)))
let term_getFirstArgument term = match term with Constructor(name, arguments) -> List.hd arguments

let context_getFlattenedInfo ctx = match ctx with Contextual(ctxList) -> List.map fst ctxList
let ctx_getEntry ctx_entry = match ctx_entry with (index, positions) -> (index - 1, List.map (fun n -> n - 1) positions)

let sig_onlyConstructors termDecl = match termDecl with DeclTrm(c1, info, ctx, arguments) -> match info with 
	| Constr(c2) -> true 
	| otherwise -> false
let sig_onlyConstructorsOfc c1 termDecl = match termDecl with DeclTrm(c2, info, ctx, arguments) -> match info with 
	| Constr(c3) -> c1 = c3 
	| otherwise -> false
let sig_onlyDestructors termDecl = match termDecl with DeclTrm(c1, info, ctx, arguments) -> match info with 
	| Destr(c2) -> true
	| otherwise -> false 
let sig_onlyDerivedNoDestructors termDecl = match termDecl with DeclTrm(c1, info, ctx, arguments) -> match info with 
	| Derived(maybeinfo) -> (match maybeinfo with 
		| None -> true
		| _ -> false)
	| otherwise -> false 
let sig_onlyDerivedDestructors termDecl = match termDecl with DeclTrm(c1, info, ctx, arguments) -> match info with 
	| Derived(maybeinfo) -> (match maybeinfo with 
		| None -> false
		| _ -> true)
	| otherwise -> false 
let sig_onlyErrorHandlers termDecl = match termDecl with DeclTrm(c1, info, ctx, arguments) -> match info with 
	| ErrorHandler -> true
	| otherwise -> false 
let sig_onlyErrors termDecl = match termDecl with DeclTrm(c1, info, ctx, arguments) -> match info with 
	| Error -> true
	| otherwise -> false 
let sig_onlyValueWithValues termDecl = match termDecl with DeclTrm(_, info, ctx, _) -> match info with 
| Constr(c) -> (List.length (context_getFlattenedInfo ctx)) > 0 
| otherwise -> false 

let sig_onlyContextual termDecl = match termDecl with DeclTrm(c, info, (Contextual ctxList), arguments) -> not (ctxList == [])
let sig_onlyAbout c1 termDecl = match termDecl with DeclTrm(c2, info, (Contextual ctxList), arguments) -> c1 == c2
	
let canonicalForTerm termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> let newVars = List.mapi (term_getFormalVarByType arguments) arguments in (Constructor(c,newVars), newVars)
let canonicalForTermNoClash termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> let newVars = List.mapi term_getFormalVar arguments in (Constructor(c,newVars), newVars)
let canonicalForType typeDecl = match typeDecl with DeclType(c, arguments) -> let newVars = List.mapi (term_getFormalVarByType arguments) arguments in (Constructor(c,newVars), newVars)
let termDelc_getOperator termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> c
let termDelc_getArgumentEntries termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> arguments
let termDelc_getCtxInfo termDecl = match termDecl with DeclTrm(c, info, ctx, arguments) -> context_getFlattenedInfo ctx
let termDecl_containTerms termDecl = List.mem (Simple("term")) (termDelc_getArgumentEntries termDecl)
let getConstructors signatureTerms = List.filter sig_onlyConstructors signatureTerms
let getConstructorsByOp c signatureTerms = List.filter (sig_onlyConstructorsOfc c) signatureTerms
let getDestructors signatureTerms = List.filter sig_onlyDestructors signatureTerms
let getDerivedNoDestructors signatureTerms = List.filter sig_onlyDerivedNoDestructors signatureTerms
let getDerivedDestructors signatureTerms = List.filter sig_onlyDerivedDestructors signatureTerms
let getDerived signatureTerms = (getDerivedNoDestructors signatureTerms) @ (getDerivedDestructors signatureTerms) 
let getErrorHandlers signatureTerms = List.filter sig_onlyErrorHandlers signatureTerms
let getErrors signatureTerms = List.filter sig_onlyErrors signatureTerms
let getNonResults signatureTerms = (getDestructors signatureTerms) @ (getDerived signatureTerms) @ (getErrorHandlers signatureTerms)
let getAllButErrorHandlers signatureTerms = (getConstructors signatureTerms) @ (getDestructors signatureTerms) @ (getDerived signatureTerms) @ (getErrors signatureTerms)
let errorPropagatingContexts signatureTerms = (List.concat (List.map termDelc_getCtxInfo (getAllButErrorHandlers signatureTerms)))
let getValuesWithValues signatureTerms = List.filter sig_onlyValueWithValues signatureTerms

let ts_containErrors ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> not((getErrors signatureTerms) = [])

let rec term_withTick index term = match term with 
	| Var(name) -> Var(name ^ "'")
	| Constructor(name, arguments) -> Constructor(name, List.take index arguments @ [term_withTick 0 (List.nth arguments index)] @ List.drop (index+1) arguments)

let info_destructedType info = match info with 
	| Destr(c) -> c
	| Derived(maybeinfo) -> match maybeinfo with Some c -> c


let rule_getOutputTerm rule = match rule with Rule(name, premises, conclusion) -> match conclusion with Formula(pred, inputs, outputs) -> List.hd outputs
let rule_getInputTerm rule = match rule with Rule(name, premises, conclusion) -> match conclusion with Formula(pred, inputs, outputs) -> List.hd inputs
let rule_getPremises rule = match rule with Rule(name, premises, conclusion) -> premises
let rule_getConclusion rule = match rule with Rule(name, premises, conclusion) -> conclusion
let rule_turnFormulaTo pred1 formula = match formula with Formula(pred2, inputs, outputs) -> Formula(pred1, inputs, outputs)
let rec term_getAllVariables term = match term with 
	| Var(name) -> [Var(name)] 
	| Constructor(c,arguments) -> List.concat (List.map term_getAllVariables arguments)
	| Application(term1,term2) -> term_getAllVariables term1 @ term_getAllVariables term2

let formula_getAllVariables formula = match formula with Formula(pred, inputs, outputs) -> List.concat (List.map term_getAllVariables inputs) @ List.concat (List.map term_getAllVariables outputs)
let rule_getAllVariables rule = match rule with Rule(name, premises, conclusion) -> (List.concat (List.map formula_getAllVariables premises)) @ (formula_getAllVariables conclusion)
let is_destructing info = sig_onlyDestructors (DeclTrm("", info, Contextual([]), []))
let toStringFromList vars = " " ^ (String.concat " " (List.map toString vars))
let getContextualTerms signatureTerms = List.filter sig_onlyContextual signatureTerms

let rule_onlyTypingRules rule = match rule with Rule(name, premises, conclusion) -> match conclusion with Formula(pred, inputs, outputs) -> pred = "typeOf"
let rule_onlyStepRules rule = match rule with Rule(name, premises, conclusion) -> match conclusion with Formula(pred, inputs, outputs) -> pred = "step"
let rule_onlyContextRules rule = match rule with Rule(name, premises, conclusion) -> String.starts_with name "ctx"
let rule_onlyAboutC c1 rule = match rule_getInputTerm rule with 
	| Constructor(c2,arguments) -> c1 = c2
	| otherwise -> false
let rec retrieveApplications term = match term with 
		  | Var(name) -> []
		  | Constructor(name, arguments) -> List.concat (List.map retrieveApplications arguments)
		  | Application(term1, term2) -> [(term1, term2)]
let retrieveApplication var term = try Some (List.assoc var (retrieveApplications term)) with Not_found -> None
let rec retrievePosition var term = match term with 
    | Var(name) -> raise (Failure "ERROR:retrievePosition, proved term is simply a variable, not allowed!")
    | Constructor(name, arguments) -> let index = find var arguments in 
		if index = 0 then match (List.hd arguments) with Constructor(name2, arguments2) -> let index = find var arguments2 in "2_" ^ (string_of_int index)
		else "1_" ^ (string_of_int index)
    | Application(term1, term2) -> raise (Failure "ERROR: retrievePosition, Application in proved term, not allowed!") 
	
let rule_seekStepOfWith c rules canonicalDecl  = match canonicalDecl with DeclTrm(canonical_c, _, _, _) -> 
	let onlyDestroyCanonical = fun rule -> match rule_getInputTerm rule with Constructor(_,arguments) -> (match List.hd arguments with 
		| Constructor(c2,_) -> canonical_c = c2 
		| otherwise -> false)
	in 
	let result = (List.filter onlyDestroyCanonical (List.filter (rule_onlyAboutC c) (List.filter rule_onlyStepRules rules))) in 
	if result = [] then None else Some (List.hd result)

let rule_seekStepOf c rules = List.hd (List.filter (rule_onlyAboutC c) (List.filter rule_onlyStepRules rules))
let rule_seekTypeOf c rules = List.hd (List.filter (rule_onlyAboutC c) (List.filter rule_onlyTypingRules rules))
let seekDeclTermOf signatureTerms c = List.hd (List.filter (sig_onlyAbout c) signatureTerms)

let toStepPremise term1 term2 = Formula("step", [term1], [term2])
let toTypeOfPremise term1 term2 = Formula("typeOf", [term1], [term2])

let unifiableByConstructor c1 rules termDecl = match rule_getOutputTerm (rule_seekTypeOf (termDelc_getOperator termDecl) rules) with
		| Constructor(c2, arguments) -> c1 = c2
		| otherwise -> true

	
