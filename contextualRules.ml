
open Batteries
open Aux
open TypedLanguage
open SafeTypedLanguage
open Values

let toStepPremiseWithTickOn index term = Formula("step", [term], [term_withTick index term])

let toContextRulesByCTX termDecl ctxinfo = match ctxinfo with (ctxposition, valuepositions) ->
	let (canonical, vars) = term_getCanonical termDecl in
	let rulename = "ctx_" ^ (term_getOperator termDecl) ^(string_of_int ctxposition) in
	let stepPremise = try toStepPremiseWithTickOn ctxposition (nthMinusOne vars ctxposition) with Failure _ -> raise(Failure((term_getOperator termDecl) ^ string_of_int(ctxposition))) in 
	let valuepremises = List.map toValuePremise (List.map (nthMinusOne vars) valuepositions) in 
	 Rule(rulename, stepPremise::valuepremises, toStepPremiseWithTickOn (ctxposition-1) canonical)
	 
let generateContextualRules termDecl = List.map (toContextRulesByCTX termDecl) (term_getContextInfo termDecl)

