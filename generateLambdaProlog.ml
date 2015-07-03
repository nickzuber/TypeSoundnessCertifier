
open Batteries
open Type_system
open Aux
open Terms
open PreservationTests
open Unix

let generateSigPreamble = "sig mycalculus.\n\nkind typ, term type.\n\n"
let generateModPreamble = "module mycalculus.\n\n"

let generateTypeExpr te = match te with 
         | Simple(typ) -> typ 
         | Abstraction(typ1,typ2) -> "(" ^ typ1 ^ " -> " ^ typ2 ^ ")"

let generateTypeEntry signatureEntry = match signatureEntry with DeclType(c,kind,constructors,deconstructors,arguments) ->
let displayArguments = if List.length arguments = 0 then "" else (String.concat " -> " (List.map generateTypeExpr arguments)) ^ " -> " in
"type " ^ c ^ " " ^ displayArguments ^ "typ."

let generateTermEntry signatureEntry = match signatureEntry with DeclTrm(c,kind,arguments) ->
let displayArguments = if List.length arguments = 0 then "" else (String.concat " -> " (List.map generateTypeExpr arguments)) ^ " -> " in
"type " ^ c ^ " " ^ displayArguments ^ "term."

let extraSigForPredicates =
"type termPred term  -> o.\n
type value term -> o.\n
type nonvalue term -> o.\n\n
type typeOf term -> typ -> o.\n
type step term -> term -> o.\n"

let generateSignature ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
generateSigPreamble ^ (String.concat "\n" (List.map generateTypeEntry signatureTypes)) ^ "\n" ^ (String.concat "\n" (List.map generateTermEntry signatureTerms))  ^ "\n\n" ^ extraSigForPredicates

let rec generateTerm term = match term with
         | Var(variable) -> variable
         | Constructor(name, arguments) -> "(" ^ name ^ " " ^ (String.concat " " (List.map generateTerm arguments)) ^ ")"
         | Application(term1, term2) -> generateTerm (Constructor(toString term1, [term2]))

let rec generateFormula formula = match formula with 
         | Formula(pred, inputs, outputs) ->
                  let argAll = (List.map generateTerm inputs) @ (List.map generateTerm outputs) in
                     pred ^ " " ^ (String.concat " " argAll)
         | Hypothetical(typ1,term,typ2) -> "(pi x\\ typeOf x " ^ (generateTerm typ1) ^ " => " ^ "typeOf " ^ (generateTerm term) ^ " " ^ (generateTerm typ2) ^ ")"
         | Generic(term1,term2) -> "(pi x\\ typeOf " ^ (generateTerm term1) ^ " " ^ (generateTerm term2) ^ ")"


let generateRule rule = match rule with Rule(name,premises,conclusion) ->
         let prePremises = List.map generateFormula premises in
         let pr = if prePremises = [] then "" else " :- " ^ (String.concat ", " prePremises) in 
           (generateFormula conclusion) ^ pr ^ ".\n"

let generateModule ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> generateModPreamble ^ (String.concat "\n" (List.map generateRule rules))

let generateTestDefinitions rule = match rule with Rule(name,premises,conclusion) ->
         let allVariables_ = (getAllVariables rule) in 
         let forallPreamble = if allVariables_ = [] then "" else "forall " ^ (String.concat " " (List.unique (List.map toString (getAllVariables rule)))) ^ ", " in 
         let testname = "test_" ^ name in 
         let displayedPremises = (List.map generateFormula premises) in
         let wrappedInBrackets = fun formula -> "{" ^ formula ^ "}" in
          "Define " ^ testname ^ " : prop by\n   " ^ testname ^ " := " ^ forallPreamble ^ String.concat " -> " (List.map wrappedInBrackets displayedPremises) ^ " -> " ^ wrappedInBrackets (generateFormula conclusion) ^ ".\n\n"


let generateTestModule ts = let testRules = rulesForPreservationTests ts in 
         let generateTestQuery = fun rule -> match rule with Rule(name,premises,conclusion) -> "Query test_" ^ name ^ ".\n\n"in 
         (String.concat "\n" (List.map generateTestDefinitions testRules)) ^ "\n" ^ (String.concat "\n" (List.map generateTestQuery testRules))

let runPreservationTests dummy = let () = chdir "generated" in let output = callAbella "abella ./mycalculusTests.thm" in let () = chdir "../" in
         let extractNameOfRule = fun line -> let n = String.length "Abella < Query test_" in String.rchop (String.sub line n ((String.length line) - n)) in 
         let spotNoSolution = fun output -> fun i -> fun line -> let ok = "ok" in  
          if String.exists line "No more" then if String.exists (List.at output (i-1)) "Query" then extractNameOfRule (List.at output (i-1)) else ok else ok in
         let okLinesGoAway = fun line -> if line = "ok" then false else true in 
         let output2 = output in
         let errorsWithOkLines = List.mapi (spotNoSolution output2) output in 
         let failingRules = List.filter okLinesGoAway errorsWithOkLines in 
          if failingRules = [] then "Type Preservation: Succesfully checked! All the reductions rules preserve types.\n" else "Type Preservation: Failed. The following reductions rules do not preserve types: " ^ String.concat ", " failingRules ^ "\n"
