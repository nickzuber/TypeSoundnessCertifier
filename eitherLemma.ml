
open Type_system
open Aux
open Terms

let eachSubGoal signatureTerms rule = match rule with Rule(name,premises,conclusion) -> 
         let constructor = getConstructorInInput conclusion in 
         let (formalTerms, formalAbstractions, theRest) = (getTermsAndTheRestByConstructor constructor signatureTerms) in 
         let hypothVars = (getFormalVariables "TermPred" (List.length formalTerms)) in 
         let applyIHtoAll = (fun h -> "Tmp : apply IH to " ^ h ^ ". case Tmp.\n") in 
         let searchToAll = (fun h -> "search.") in 
          String.concat "" (List.map applyIHtoAll hypothVars) ^ " search. " ^ (String.concat " " (List.map searchToAll hypothVars)) ^ "\n"

let generateEitherLemma ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> 
         let theorem = "Theorem eitherValueOrNot : forall E, {termPred E} -> {value E} \\/ {nonvalue E}.\n" in
         let preambleproof = "induction on 1. intros Main. TermPred1 : case Main.\n"in 
         let proof = String.concat "" (List.map (eachSubGoal signatureTerms) (List.filter Terms.onlyTermPredRules rules)) in
          theorem ^ preambleproof ^ proof ^ "\n"
