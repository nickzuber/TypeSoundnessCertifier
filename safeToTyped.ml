
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Values
open ContextualRules
open ErrorManagement

let compile sl = 
	let types = sl_getTypes sl in 
	let others = sl_getOthers sl in 
	let errorSpec = sl_getError sl in 
	let signatureTypes = List.map specType_getSig types in 
	let signatureConstructors = List.map specTerm_getSig (List.concat (List.map specType_getConstructors types)) in 
	let signatureEliminators = List.map specTerm_getSig (List.concat (List.map specType_getEliminators types)) in 
	let signatureOthers = (List.map specTerm_getSig others) in 
	let signatureOfAllButErrors = signatureConstructors @ signatureEliminators @ signatureOthers in
	let signatureErrors = if is_none errorSpec then [] else specTerm_getSig (specError_getError errorSpec) :: (List.map specTerm_getSig (specError_getHandlers errorSpec)) in 
	let signatureTerms = signatureOfAllButErrors @ signatureErrors in 
	let ruleForConstructors = sl_getReductionRulesOfConstructors types in 
	let ruleForEliminators = sl_getReductionRulesOfEliminators types in 
	let ruleForOthers = List.concat (List.map specTerm_getRules others) in 
	let ruleForErrors = if is_none errorSpec then [] else List.concat (List.map specTerm_getRules (specError_getHandlers errorSpec)) in 
	let valueDefinitions = List.map generateValues signatureConstructors in 
	let contextualRules = List.concat (List.map generateContextualRules signatureTerms) in 
	let errorManagement = generateErrorManagement errorSpec signatureOfAllButErrors in
	 TypedLanguage(signatureTypes, signatureTerms, ruleForConstructors @ ruleForEliminators @ ruleForOthers @ ruleForErrors @ valueDefinitions @ contextualRules @ errorManagement)
	