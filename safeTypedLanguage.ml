
open Batteries
open Option
open Aux
open TypedLanguage

type errorname = string
type typingrule = rule
type reductionrule = rule 

type term_specification = 
  | SpecTerm of signature_term * typingrule * reductionrule list 


type constructor_term = term_specification 
type eliminator_term = term_specification
type supplementalTerm_specification = term_specification
type error_specification = SpecError of term_specification * term_specification list

type type_specification = 
| SpecType of signature_type * constructor_term list * eliminator_term list

type safe_typed_language =
  | SafeTypedLanguage of type_specification list * supplementalTerm_specification list * (error_specification option)

let emptySL = SafeTypedLanguage([], [], None)


let term_getFormalVarByType arguments preIndex typeEntry = let index = preIndex + 1 in match typeEntry with 
  | Simple("term") -> Var("E" ^ (string_of_int index))
  | Abstraction(typ1, "term") -> Var("R" ^ (string_of_int index))
  | Abstraction(typ1, "typ") -> Var("U" ^ (string_of_int index))
  | Simple("typ") -> Var("T" ^ (string_of_int index))

let term_getFormalVar index typeEntry = Var("Arg" ^ (string_of_int (index+1)))

	
let specType_getSig specType = match specType with SpecType(signature, constructors, eliminators) -> signature
let specType_getTypeName specType = type_getOperator (specType_getSig specType)
let specType_getConstructors specType = match specType with SpecType(signature, constructors, eliminators) -> constructors 
let specType_getEliminators specType = match specType with SpecType(signature, constructors, eliminators) -> eliminators
let specType_addEliminator specType eliminator = match specType with SpecType(signature, constructors, eliminators) -> SpecType(signature, constructors, removeDuplicates (eliminator :: eliminators))
let specType_compose specType1 specType2 = if specType_getTypeName specType1 = specType_getTypeName specType2 then [SpecType(specType_getSig specType1, specType_getConstructors specType1 @ specType_getConstructors specType2, specType_getEliminators specType1 @ specType_getEliminators specType2)] else [specType1 ; specType2]
let rec specTypes_flatten (specTypes1, specTypes2) = match (specTypes1, specTypes2) with 
| ([], []) -> ([], [])
| ([], specType) -> ([], specType)
| (specType1 :: rest1, specTypes) -> let (theOne, nonTheOne) = List.partition (fun spec -> (specType_getTypeName specType1) = (specType_getTypeName spec)) specTypes in if theOne = [] then specTypes_flatten (rest1, specType1 :: specTypes) else specTypes_flatten (rest1, (specType_compose specType1 (List.hd theOne)) @ nonTheOne)
	
let sl_getAllEliminators sl = match sl with SafeTypedLanguage(types, others, errorSpec) -> List.concat (List.map specType_getEliminators types)

let specTerm_getSig specTerm = match specTerm with SpecTerm(signature, typingrule, reductionrules) -> signature
let specTerm_getTyping specTerm = match specTerm with SpecTerm(signature, typingrule, reductionrules) -> typingrule
let specTerm_getReduction specTerm = match specTerm with SpecTerm(signature, typingrule, reductionrules) -> reductionrules
let specTerm_getOperator specTerm = term_getOperator (specTerm_getSig specTerm)
let specTerm_getRules specTerm = specTerm_getTyping specTerm :: specTerm_getReduction specTerm
let specTerms_getAllRules specTermList = List.concat (List.map specTerm_getRules specTermList)
let specTerms_getAllTypingRules specTermList = List.filter rule_isTypingRule (specTerms_getAllRules specTermList)
let specError_getError errorSpec = match get errorSpec with SpecError(error, errorHandlers) -> error
let specError_getHandlers errorSpec = if is_none errorSpec then [] else match get errorSpec with SpecError(error, errorHandlers) -> errorHandlers
let specError_getHandlersTypingRules errorSpec = if is_none errorSpec then [] else List.filter rule_isTypingRule (List.concat (List.map specTerm_getRules (specError_getHandlers errorSpec)))
let specError_compose errorSpec1 errorSpec2 = if is_none errorSpec1 then errorSpec2 else if is_none errorSpec2 then errorSpec1 else if errorSpec1 = errorSpec2 then errorSpec1 else raise(Failure "error in composing error specifications")
let type_getCanonical typeDecl = match typeDecl with DeclType(c, arguments) -> let newVars = List.mapi (term_getFormalVarByType arguments) arguments in (Constructor(c,newVars), newVars)
let term_getCanonical termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> let newVars = List.mapi (term_getFormalVarByType arguments) arguments in (Constructor(c,newVars), newVars)
let term_getCanonicalNoClash termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> let newVars = List.mapi term_getFormalVar arguments in (Constructor(c,newVars), newVars)

let specType_getConstructorsNAMES specType = List.map term_getOperator (List.map specTerm_getSig (specType_getConstructors specType))

let term_decls_lookup tl c =
	let onlyByC term = term_getOperator term = c in 
	List.hd (List.filter onlyByC (tl_getTerms tl))

let types_decls_lookup tl c =
	let onlyByC term = type_getOperator term = c in 
	List.hd (List.filter onlyByC (tl_getTypes tl))

let unifiableWithConstructor c1 rule = match rule_getOutputTerm rule with
		| Constructor(c2, arguments) -> c1 = c2
		| otherwise -> true (* otherwise can be for instance a variable, which unifies *)

let toStepPremise term1 term2 = Formula("step", [term1], [term2])
let toTypeOfPremise term1 term2 = Formula("typeOf", [term1], [term2])

let sl_getTypes sl = match sl with SafeTypedLanguage(types, others, errorSpec) -> types
let sl_getOthers sl = match sl with SafeTypedLanguage(types, others, errorSpec) -> others
let sl_getError sl = match sl with SafeTypedLanguage(types, others, errorSpec) -> errorSpec
let sl_getErrorConstructor sl = term_getOperator (specTerm_getSig (specError_getError (sl_getError sl)))
let sl_addType sl typeSpec = match sl with SafeTypedLanguage(types, others, errorSpec) -> SafeTypedLanguage(removeDuplicates (typeSpec :: types), others, errorSpec)
let sl_addTypes sl types = match sl with SafeTypedLanguage(_, others, errorSpec) -> SafeTypedLanguage(types, others, errorSpec)
let sl_addDerived sl derived = match sl with SafeTypedLanguage(types, others, errorSpec) -> SafeTypedLanguage(types, removeDuplicates (derived :: others), errorSpec)
let sl_addErrorHandler sl termDecl rule reductionRules = let newErrorHandler = SpecTerm(termDecl, rule, reductionRules) in match sl with SafeTypedLanguage(types, others, errorSpec) -> match errorSpec with Some SpecError(error, errorHandlers) -> SafeTypedLanguage(types, others, Some (SpecError(error, newErrorHandler :: errorHandlers)))
let sl_removeType sl typ = match sl with SafeTypedLanguage(types, others, errorSpec) -> let noTyp specType = not(type_getOperator typ = specType_getTypeName specType) in SafeTypedLanguage(List.filter noTyp types, others, errorSpec) 
let sl_containErrors sl = is_some (sl_getError sl)
let sl_isConstructor sl termDecl = List.exists (fun specTerms -> (List.mem termDecl (List.map specTerm_getSig specTerms))) (List.map specType_getConstructors (sl_getTypes sl))
let sl_lookup_typeSpec sl c = let searchbyname typeSpec = specType_getTypeName typeSpec = c in try List.hd (List.filter searchbyname (sl_getTypes sl)) with Failure e -> raise(Failure ("sl_lookup_typeSpec: " ^ c))
let sl_withError errorDecl errorTypingRule = SafeTypedLanguage([], [], Some (SpecError(SpecTerm(errorDecl, errorTypingRule, []), [])))
let sl_withConstructor typ term rule = SafeTypedLanguage([SpecType(typ, [SpecTerm(term, rule, [])], [])], [], None)
let sl_withEliminator sl typ term rule reductionRules = let eliminator = SpecTerm(term, rule, reductionRules) in 
	sl_addType (sl_removeType sl typ) (specType_addEliminator (sl_lookup_typeSpec sl (type_getOperator typ)) eliminator)
let sl_withDerived sl term rule reductionRules = let derived = SpecTerm(term, rule, reductionRules) in sl_addDerived sl derived
let sl_compose sl1 sl2 = SafeTypedLanguage((sl_getTypes sl1) @ (sl_getTypes sl2), 
										sl_getOthers sl1 @ sl_getOthers sl2, 
										specError_compose (sl_getError sl1) (sl_getError sl2))
let sl_getRulesOfEliminators typeSpec = List.concat (List.map specTerm_getRules (List.concat (List.map specType_getEliminators typeSpec)))
let sl_getRulesOfConstructors typeSpec = List.concat (List.map specTerm_getRules (List.concat (List.map specType_getConstructors typeSpec)))

let sl_getAllRules sl = let ruleForErrors = if is_none (sl_getError sl) then [] else List.concat (List.map specTerm_getRules (specError_getHandlers (sl_getError sl))) @ [List.hd (specTerm_getRules (specError_getError (sl_getError sl)))] in 
	sl_getRulesOfConstructors (sl_getTypes sl) @ sl_getRulesOfEliminators (sl_getTypes sl) @  List.concat (List.map specTerm_getRules (sl_getOthers sl)) @ ruleForErrors 

let rule_checkEliminates listOfConstructors rule =  
	if term_isConstructor (rule_getInputTerm rule) then 
		let args = term_getArguments (rule_getInputTerm rule) in
		if args = [] then false else if term_isConstructor (List.hd args) then List.mem (term_getConstructor (List.hd args)) listOfConstructors else false 
	else false

let rule_checkFreeReduction rule = 
	if term_isConstructor (rule_getInputTerm rule) then List.for_all term_isVar (term_getArguments (rule_getInputTerm rule))
	else false

let rule_typeCheckFirst rule = if (rule_getPremises rule) = [] then false else match formula_getFirstOutput (List.hd (rule_getPremises rule)) with 
	| Constructor(c, args) -> true
	| otherwise -> false
let rule_getFirstTypeCheck rule = match List.hd (rule_getPremises rule) with Formula(pred, inputs, outputs) -> term_getConstructor (List.hd outputs)


