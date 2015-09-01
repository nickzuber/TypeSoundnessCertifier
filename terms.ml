
open Type_system
open Aux
open Batteries

let termPredicate = "termPred"

let toTermPredFormula term = Formula(termPredicate, [term], [])

let toTermPred_byDecl signatureEntry = match signatureEntry with DeclTrm(c,kind,ctx, arguments) -> 
                           let (terms, abstractions, theRest) = getTermsAndTheRest arguments in 
			    Rule(termPredicate^"_"^c, (List.map toTermPredFormula terms), toTermPredFormula (Constructor(c, terms @ abstractions @ theRest)))
	  
let toTermPred ts =  match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> List.map toTermPred_byDecl signatureTerms


let generateTermPred ts = Type_system.extend ts (toTermPred ts)

let onlyValueRules rule = match rule with
			   | Rule(name,premises,Formula("value", inputs, outputs)) -> true
			   | _ -> false
let onlyNonValueRules rule = match rule with
			   | Rule(name,premises,Formula("nonvalue", inputs, outputs)) -> true
			   | _ -> false
let onlyTermPredRules rule = match rule with
			   | Rule(name,premises,Formula(predicate, inputs, outputs)) -> String.starts_with predicate termPredicate
			   | _ -> false

let onlyTypingRules rule = match rule with Rule(name,premises,Formula(pred, inputs, outputs)) -> pred = Type_system.typing
let onlyStepRules rule = match rule with Rule(name,premises,Formula(pred, inputs, outputs)) -> pred = "step"
let onlyContextRules rule = match rule with Rule(name,premises,Formula(pred, inputs, outputs)) -> String.starts_with name "ctx_"

let onlyTypingRulesOfValues signatureTypes rule = match rule with Rule(name,premises,Formula(pred, inputs, outputs)) -> if pred = Type_system.typing then let constructor = (getConstructor (List.hd inputs)) in (isTypeConstructor signatureTypes constructor) else false

let onlyRulesOfOutput constructor rule = match rule with Rule(name,premises,Formula(pred, inputs, outputs)) -> if getConstructor (List.hd outputs) = constructor then true else false
