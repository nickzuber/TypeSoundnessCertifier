
open Batteries
open Aux
open TypedLanguage
open Ldl
open ListManagement
open Values

let toStepPremiseWithTickOn index term = Formula("step", [term], [term_withTick index term])

let generateContextualRules_list termDecl = 
	let c = term_getOperator termDecl in 
	let labelVar = [Var "L"] in 
	let restVar = [(Var "Rest")] in 
	let restVar' = List.map toTicked restVar in (* silly to apply map for one element, but it makes it quick *)
	let endingVars = (Var "E") :: restVar in 
	let endingVarsEticked = (Var "E'") :: restVar in 
	let endingVarsRestTicked = (Var "E") :: restVar' in 
	 match term_getContextualPositions termDecl with 
		| [3] -> []  (* No contexual *)
		| n -> let firstRule = [Rule ("step_" ^ c ^ "_1", 
									[toStepPremise (Var "E") (Var "E'")], 
									toStepPremise (Constructor(c, [Constructor(consList c, labelVar @ endingVars)])) (Constructor(c, [Constructor(consList c, labelVar @ endingVarsEticked)]))
									)] in 
				let valuehoodForTheExpression = match n with 
					| [1] -> [toValuePremise (Var "E")]     (* Sequential *)
					| [2] -> []  (* Parallel *)
				in 
				firstRule @
				[Rule ("step_" ^ c ^ "_2", 
							[toStepPremise (Constructor(c, restVar)) (Constructor(c, restVar'))]
							@ valuehoodForTheExpression
							, 
							toStepPremise (Constructor(c, [Constructor(consList c, labelVar @ endingVars)])) (Constructor(c, [Constructor(consList c, labelVar @ endingVarsRestTicked)]))
													)]
													
let toContextRulesByCTX termDecl ctxinfo = match ctxinfo with (ctxposition, valuepositions) ->
	let (canonical, vars) = term_getCanonical termDecl in
	let rulename = "ctx_" ^ (term_getOperator termDecl) ^(string_of_int ctxposition) in
	let stepPremise = try toStepPremiseWithTickOn ctxposition (nthMinusOne vars ctxposition) with Failure _ -> raise(Failure((term_getOperator termDecl) ^ string_of_int(ctxposition))) in 
	let valuepremises = List.map toValuePremise (List.map (nthMinusOne vars) valuepositions) in 
	 Rule(rulename, stepPremise::valuepremises, toStepPremiseWithTickOn (ctxposition-1) canonical)
	 
let generateContextualRules termDecl = 
	if termDecl_isList termDecl 
		then generateContextualRules_list termDecl
		else List.map (toContextRulesByCTX termDecl) (term_getContextInfo termDecl)

