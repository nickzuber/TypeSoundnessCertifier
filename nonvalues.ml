
open Type_system
open Terms
open Values


let toNonValues_byRule values rule = match rule with 
   | Rule(name,premises,conclusion) -> let constructor = (getConstructorInInput conclusion) in
			               let valueRule = (lookupRuleByConstructor constructor values) in
			               let whichArgument = fun premise -> toString (getTermInInput premise) in
			                let ruleForEach = (fun premise -> Rule("nonvalue_" ^ constructor ^ (whichArgument premise), (premises @ [turnFormulaTo "nonvalue" premise]), (turnFormulaTo "nonvalue") conclusion)) in 
			                 if valueRule == [] then [Rule("nonvalue_"^constructor, premises, (turnFormulaTo "nonvalue") conclusion)]
			                 else (List.map ruleForEach (Type_system.getPremises (List.hd valueRule)))

let toNonValueDefs ts =  match ts with 
   | TypeSystem(signatureTypes,signatureTerms,rules) -> let values = List.filter onlyValueRules rules in
                                                         let terms = List.filter onlyTermPredRules rules in 
                                                          List.concat (List.map (toNonValues_byRule values) terms)

let generateNonValues ts = Type_system.extend ts (toNonValueDefs ts)
let generateNonValues_ ts = Type_system.extend (generateValues (generateTermPred ts)) (toNonValueDefs (generateValues (generateTermPred ts)))

