
open Batteries
open Aux
open Type_system

let toErrorPremise term = Formula("error", [term], [])

let toErrorContextsByCTX termDecl ctx_entry = match ctx_getEntry ctx_entry with (index, positions) -> 
	let (canonical, vars) = (canonicalForTerm termDecl) in
	let c = termDelc_getOperator termDecl in
	let errorVar = (List.nth vars index) in 
	let rulename = "error_ctx_"^c^(string_of_int index) in
	 Rule(rulename, [toErrorPremise errorVar], toStepPremise canonical errorVar)

let generateErrorContexts ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> 
	let toErrorContexts termDecl = 
		(match termDecl with DeclTrm(c, info, ctx, arguments) -> 
			match ctx with Contextual(ctx_entries) -> List.map (toErrorContextsByCTX termDecl) ctx_entries) in 
	 if ts_containErrors ts then Type_system.extend ts (List.concat (List.map toErrorContexts (getAllButErrorHandlers signatureTerms))) else ts
