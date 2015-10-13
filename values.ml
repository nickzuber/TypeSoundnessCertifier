
open Batteries
open Type_system
open Aux

let toValuePremise term = Formula("value", [term], [])

let toValueDefinitionsByCTX termDecl ctx_entry = 
	let (canonical, vars) = (canonicalForTerm termDecl) in
	let c = termDelc_getOperator termDecl in
	let rulename = "value_"^c in
	match ctx_entry with 
		| None -> Rule(rulename, [], toValuePremise canonical)
		| Some (index, positions) -> let valueVars = List.map (nthMinusOne vars) (index::positions) in Rule(rulename, List.map toValuePremise valueVars, toValuePremise canonical) 

	(* let sd = (List.map print_int (index::positions)) in Rule(rulename, [], toValuePremise canonical) *)
	
let generateValues ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> 
	let toValueDefinitions termDecl = 
		(match termDecl with DeclTrm(c, info, ctx, arguments) -> 
		 match ctx with Contextual(ctx_entries) -> if ctx_entries == [] then toValueDefinitionsByCTX termDecl None else toValueDefinitionsByCTX termDecl (Some (List.last ctx_entries))) in 
	 Type_system.extend ts (List.map toValueDefinitions (getConstructors signatureTerms))

	 (* Values generation: only constructors. We also look if we allow reductions on such constructors. 
	 So, we take the last entry of ctx. Assuming it contains the 'greatest' info *)
