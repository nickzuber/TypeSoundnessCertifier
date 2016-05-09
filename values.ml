
open Batteries
open Aux
open TypedLanguage
open Ldl

let generateValues termDecl = 
	let (canonical, vars) = term_getCanonical termDecl in
	let rulename = "value_"^ (term_getOperator termDecl) in
	let premises = List.map toValuePremise (List.map (nthMinusOne vars) (term_getValPositions termDecl)) in
	 Rule(rulename, premises, toValuePremise canonical)

	 (* Values generation: only constructors. We also look if we allow reductions on such constructors. 
	 So, we take the last entry of ctx. Assuming it contains the 'greatest' info *)
