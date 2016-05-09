
open Batteries
open Option
open Aux
open TypedLanguage
open Ldl

let toErrorPremise term = Formula("error", [term], [])

let generateError termDecl = 
	 	let (canonical, vars) = term_getCanonical termDecl in
		let valuePremises = List.map toValuePremise (List.map (nthMinusOne vars) (term_getValPositions termDecl)) in 
	 	 Rule("error", valuePremises, toErrorPremise canonical)

let toErrorContextsByCTX termDecl position = 
	 	let (canonical, vars) = term_getCanonical termDecl in
	 	let errorVar = (nthMinusOne vars position) in 
	 	let rulename = "error_ctx_" ^ term_getOperator termDecl ^(string_of_int position) in
	 	 Rule(rulename, [toErrorPremise errorVar], toStepPremise canonical errorVar)

let toErrorContextsByOp termDecl = List.map (toErrorContextsByCTX termDecl) (List.map fst (term_getContextInfo termDecl))

let generateErrorManagement errorSpec signatureOfAllButErrorHandlers = if is_none errorSpec then [] else
	let errorDefinition = generateError (specTerm_getSig (specError_getError errorSpec)) in 
	let errorTypingRule = List.hd (specTerm_getRules (specError_getError errorSpec)) in 
	let errorContextualRules = List.concat (List.map toErrorContextsByOp signatureOfAllButErrorHandlers) in 
	 errorDefinition :: errorTypingRule :: errorContextualRules

(*
let generateTypingError termDecl = 
	 	let (canonical, vars) = term_getCanonical termDecl in
	 	 Rule("errorTyping", [], toTypeOfPremise canonical (Var("T")))
	
*)