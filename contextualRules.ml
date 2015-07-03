
open Aux
open Type_system
open Terms

let rec changeTermArgumentAt arg term = match term with 
  | Var(name) -> if arg = Var(name) then Var(toStringWith' arg) else term
  | Constructor(name, arguments) -> Constructor(name, List.map (changeTermArgumentAt arg) arguments)

let turnIntoStep predToChange rule = match rule with Rule(name,premises,conclusion) ->
               let nameOfRule = Aux.stringReplace "nonvalue" "ctx" name in 
               let Formula(pred, inputs, outputs) = (seekPremise predToChange premises) in
               let newVar = changeTermArgumentAt (List.hd inputs) (List.hd inputs) in
               let newPremise = Formula("step", inputs, [newVar]) in
               let newconclusion = Formula("step", [getTermInInput conclusion], [changeTermArgumentAt (List.hd inputs) (getTermInInput conclusion)]) in
                 Rule(nameOfRule ^ (toString (List.hd inputs)) , [newPremise], newconclusion)

let generateEachContextualRules signatureTypes rule = match rule with Rule(name,premises,conclusion) ->
               let provedTerm = (getTermInInput conclusion) in 
               let constructor = getConstructor provedTerm in
               let produce = fun provedTerm -> fun premise -> turnIntoStep "termPred" (Rule(name, [premise], conclusion)) in
               if isTypeConstructor signatureTypes constructor then [(turnIntoStep "nonvalue" rule)] else List.map (produce provedTerm) premises

let generateContextualRules ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
               let nonValues = List.filter onlyNonValueRules rules in 
                List.concat (List.map (generateEachContextualRules signatureTypes) nonValues)

let addContextualRules ts = extend ts (generateContextualRules ts)
