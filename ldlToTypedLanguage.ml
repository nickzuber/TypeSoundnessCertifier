
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl
open Values
open ContextualRules
open ErrorManagement

let compile ldl = 
	let types = ldl_getTypes ldl in 
	let derived = ldl_getDerived ldl in 
	let errorSpec = ldl_getError ldl in 
	let signatureTypes = List.map specType_getSig types in 
	let signatureConstructors = List.map specTerm_getSig (List.concat (List.map specType_getConstructors types)) in 
	let signatureEliminators = List.map specTerm_getSig (List.concat (List.map specType_getEliminators types)) in 
	let signatureDerived = (List.map specTerm_getSig derived) in 
	let signatureOfAllButError = signatureConstructors @ signatureEliminators @ signatureDerived in
	let signatureErrorHandlers = if is_none errorSpec then [] else List.map specTerm_getSig (specError_getHandlers errorSpec) in 
	let signatureError = if is_none errorSpec then [] else [specTerm_getSig (specError_getError errorSpec)] in 
	let signatureTerms = signatureOfAllButError @ signatureErrorHandlers @ signatureError in 
	let ruleForConstructors = ldl_getRulesOfConstructors types in 
	let ruleForEliminators = ldl_getRulesOfEliminators types in 
	let ruleForDerived = List.concat (List.map specTerm_getRules derived) in 
	let ruleForErrorHandlers = if is_none errorSpec then [] else List.concat (List.map specTerm_getRules (specError_getHandlers errorSpec)) in 
	let valueDefinitions = List.map generateValues signatureConstructors in 
	let contextualRules = List.concat (List.map generateContextualRules signatureTerms) in 
	let errorManagement = generateErrorManagement errorSpec (signatureOfAllButError @ signatureError) in
	 TypedLanguage(signatureTypes, signatureTerms, ruleForConstructors @ ruleForEliminators @ ruleForDerived @ ruleForErrorHandlers @ valueDefinitions @ contextualRules @ errorManagement)
	