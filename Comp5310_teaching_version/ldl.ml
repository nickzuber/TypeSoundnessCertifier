
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

let emptyLDL = SafeTypedLanguage([], [], None)

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

let specType_getConstructorsNAMES specType = List.map term_getOperator (List.map specTerm_getSig (specType_getConstructors specType))

let unifiableWithConstructor c1 rule = match rule_getOutputTerm rule with
		| Constructor(c2, arguments) -> c1 = c2 
		| otherwise -> true (* otherwise can be for instance a variable, which unifies *)

let toStepPremise term1 term2 = Formula("step", [term1], [term2])
let toTypeOfPremise term1 term2 = Formula("typeOf", [term1], [term2])

let ldl_getTypes ldl = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> types
let ldl_getDerived ldl = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> derived
let ldl_getError ldl = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> errorSpec
let ldl_getErrorConstructor ldl = term_getOperator (specTerm_getSig (specError_getError (ldl_getError ldl)))
let ldl_getAllConstructors ldl = List.concat (List.map specType_getConstructors (ldl_getTypes ldl))
let ldl_getAllEliminators ldl = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> List.concat (List.map specType_getEliminators types)
let ldl_addType ldl typeSpec = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> SafeTypedLanguage(removeDuplicates (typeSpec :: types), derived, errorSpec)
let ldl_addTypes ldl types = match ldl with SafeTypedLanguage(_, derived, errorSpec) -> SafeTypedLanguage(types, derived, errorSpec)
let ldl_addDerived ldl terms = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> SafeTypedLanguage(types, removeDuplicates (terms :: derived), errorSpec)
let ldl_addErrorHandler ldl termDecl rule reductionRules = let newErrorHandler = SpecTerm(termDecl, rule, reductionRules) in match ldl with SafeTypedLanguage(types, derived, errorSpec) -> match errorSpec with Some SpecError(error, errorHandlers) -> SafeTypedLanguage(types, derived, Some (SpecError(error, newErrorHandler :: errorHandlers)))
let ldl_removeType ldl typ = match ldl with SafeTypedLanguage(types, derived, errorSpec) -> let noTyp specType = not(type_getOperator typ = specType_getTypeName specType) in SafeTypedLanguage(List.filter noTyp types, derived, errorSpec) 
let ldl_containErrors ldl = is_some (ldl_getError ldl)
let ldl_isConstructor ldl termDecl = List.exists (fun specTerms -> (List.mem termDecl (List.map specTerm_getSig specTerms))) (List.map specType_getConstructors (ldl_getTypes ldl))
let ldl_lookup_typeSpec ldl c = let searchbyname typeSpec = specType_getTypeName typeSpec = c in try List.hd (List.filter searchbyname (ldl_getTypes ldl)) with Failure e -> raise(Failure ("ldl_lookup_typeSpec: " ^ c))
let ldl_lookup_constructorTermSpec ldl op = let searchbyname termSpec = specTerm_getOperator termSpec = op in try List.hd (List.filter searchbyname (ldl_getAllConstructors ldl)) with Failure e -> raise(Failure ("ldl_lookup_constructorTermSpec: " ^ op))
let ldl_withError errorDecl errorTypingRule = SafeTypedLanguage([], [], Some (SpecError(SpecTerm(errorDecl, errorTypingRule, []), [])))
let ldl_withConstructor typ term rule = SafeTypedLanguage([SpecType(typ, [SpecTerm(term, rule, [])], [])], [], None)
let ldl_withEliminator ldl typ term rule reductionRules = let eliminator = SpecTerm(term, rule, reductionRules) in 
	ldl_addType (ldl_removeType ldl typ) (specType_addEliminator (ldl_lookup_typeSpec ldl (type_getOperator typ)) eliminator)
let ldl_withDerived ldl term rule reductionRules = let derived = SpecTerm(term, rule, reductionRules) in ldl_addDerived ldl derived
let ldl_compose ldl1 ldl2 = SafeTypedLanguage((ldl_getTypes ldl1) @ (ldl_getTypes ldl2), 
										ldl_getDerived ldl1 @ ldl_getDerived ldl2, 
										specError_compose (ldl_getError ldl1) (ldl_getError ldl2))

let ldl_addValueDefinitions ldl (c, positions) = 
	let constructors_addValueDefinitions (c, positions) termSpec = match termSpec with SpecTerm(signature, typingrule, reductionrules) -> match signature with DeclTrm(c2, valpos, ctx, arguments) -> let newsignature = (if c = c2 then DeclTrm(c2, positions, ctx, arguments) else DeclTrm(c2, valpos, ctx, arguments)) in SpecTerm(newsignature, typingrule, reductionrules) in 
	let types_addValueDefinitions (c, positions) typeSpec = match typeSpec with SpecType(signature, constructors, eliminators) -> SpecType(signature, List.map (constructors_addValueDefinitions (c, positions)) constructors, eliminators) in 
		match ldl with SafeTypedLanguage(types, derived, errorSpec) -> SafeTypedLanguage(List.map (types_addValueDefinitions (c, positions)) types, derived, errorSpec)


let ldl_getRulesOfEliminators typeSpecs = List.concat (List.map specTerm_getRules (List.concat (List.map specType_getEliminators typeSpecs)))
let ldl_getRulesOfConstructors typeSpecs = List.concat (List.map specTerm_getRules (List.concat (List.map specType_getConstructors typeSpecs)))
let ldl_getErrorDeclaration ldl = specError_getError (ldl_getError ldl)

let ldl_getTermDeclForConstructors ldl = (List.map specTerm_getSig (List.concat (List.map specType_getConstructors (ldl_getTypes ldl))))

let ldl_getAllRules ldl = let ruleForErrors = if is_none (ldl_getError ldl) then [] else List.concat (List.map specTerm_getRules (specError_getHandlers (ldl_getError ldl))) @ [List.hd (specTerm_getRules (specError_getError (ldl_getError ldl)))] in 
	ldl_getRulesOfConstructors (ldl_getTypes ldl) @ ldl_getRulesOfEliminators (ldl_getTypes ldl) @  List.concat (List.map specTerm_getRules (ldl_getDerived ldl)) @ ruleForErrors 

let rule_checkEliminates listOfConstructors rule =  
	if term_isConstructor (rule_getInputTerm rule) then 
		let args = term_getArguments (rule_getInputTerm rule) in
		if args = [] then false else if term_isConstructor (List.hd args) then List.mem (term_getConstructor (List.hd args)) listOfConstructors else false 
	else false

let rule_checkEliminatesAll rules c = List.exists (rule_checkEliminates [c]) rules

let rule_checkFreeReduction rule = 
	if term_isConstructor (rule_getInputTerm rule) then List.for_all term_isVar (term_getArguments (rule_getInputTerm rule))
	else false

let rule_typeCheckFirst rule = if (rule_getPremises rule) = [] then false else match formula_getFirstOutput (List.hd (rule_getPremises rule)) with 
	| Constructor(c, args) -> true
	| otherwise -> false
let rule_getFirstTypeCheck_prem rule = List.hd (rule_getPremises rule) 
let rule_getFirstTypeCheck rule = match List.hd (rule_getPremises rule) with Formula(pred, inputs, outputs) -> term_getConstructor (List.hd outputs)
let termDecl_removePrincipalArg_fromContexts termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> DeclTrm(c, valpos, List.tl ctx, arguments)
