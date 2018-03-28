
open Batteries
open Aux
open TypedLanguage
open Ldl
open ListManagement

let generateValues_list termDecl = 
	let c = term_getOperator termDecl in 
	let restVar = [(Var "Rest")] in 
	let endingVars = (Var "V") :: restVar in 
	let valuehoodConditions = match term_getValPositions termDecl with 
		| [1] -> [toValuePremise (Var "V") ; toValuePremise (Constructor(c,restVar))]   (* ALL: all must be values, i.e. value V, value (record Rest) *)
		| [2] -> [toValuePremise (Var "V")]   (* FIRST: first must be value, i.e. value V *)
		| [3] -> []   (* NONE: none must be value, i.e. no premises *)
	in 
	 [
	  Rule("value_" ^ emptyList c, [], toValuePremise (Constructor(c, [Constructor(emptyList c,[])]))) ;
  	  Rule("value_" ^ consList c, valuehoodConditions, toValuePremise (Constructor(c, [Constructor(consList c, [Var "L"] @ endingVars)]))) ;
	  ]
	  
let generateValues termDecl = 
	if termDecl_isList termDecl then generateValues_list termDecl else 
	let (canonical, vars) = term_getCanonical termDecl in
	let rulename = "value_" ^ (term_getOperator termDecl) in
	let premises = List.map toValuePremise (List.map (nthMinusOne vars) (term_getValPositions termDecl)) in
	 [Rule(rulename, premises, toValuePremise canonical)]

