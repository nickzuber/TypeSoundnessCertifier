
open Batteries
open Aux
open Type_system
open Values

let toStepPremiseWithTickOn index term = Formula("step", [term], [term_withTick index term])
			
let toContextRulesByCTX termDecl ctx_entry = match ctx_getEntry ctx_entry with (index, positions) -> 
	let (canonical, vars) = (canonicalForTerm termDecl) in
	let c = termDelc_getOperator termDecl in
	let rulename = "ctx_"^c^(string_of_int index) in
	let valueVars = List.map (List.nth vars) positions in 
	let stepPremise = toStepPremiseWithTickOn 0 (List.nth vars index) in 
	 Rule(rulename, stepPremise::(List.map toValuePremise valueVars), toStepPremiseWithTickOn index canonical)

let generateContextualRules ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> 
	let toContextRules termDecl = 
		(match termDecl with DeclTrm(c, info, ctx, arguments) -> 
			match ctx with Contextual(ctx_entries) -> List.map (toContextRulesByCTX termDecl) ctx_entries) in 
	 Type_system.extend ts (List.concat (List.map toContextRules signatureTerms))
