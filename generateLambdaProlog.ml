
open Batteries
open Aux
open TypedLanguage
open SafeTypedLanguage
open Proof

let generateSigPreamble tsName = "sig " ^ tsName ^ ".\n\nkind typ, term type.\n\n"
let generateModPreamble tsName = "module " ^ tsName ^ ".\n\n"
let generateThmPreamble tsName = "Specification \"" ^ tsName ^ "\".\n\n"

let generateTypeExpr te = match te with 
         | Simple(typ) -> typ 
         | Abstraction(typ1,typ2) -> "(" ^ typ1 ^ " -> " ^ typ2 ^ ")"

let generateTypeEntry signatureEntry = match signatureEntry with DeclType(c,arguments) ->
let displayArguments = if List.length arguments = 0 then "" else (String.concat " -> " (List.map generateTypeExpr arguments)) ^ " -> " in
"type " ^ c ^ " " ^ displayArguments ^ "typ."

let generateTermEntry signatureEntry = match signatureEntry with DeclTrm(c,info,ctx,arguments) ->
let displayArguments = if List.length arguments = 0 then "" else (String.concat " -> " (List.map generateTypeExpr arguments)) ^ " -> " in
"type " ^ c ^ " " ^ displayArguments ^ "term."

let extraSigForPredicates =
"type value term -> o.\n
type error term -> o.\n\n
type typeOf term -> typ -> o.\n
type step term -> term -> o.\n"

(*
type nonvalue term -> o.\n\n
type termPred term  -> o.\n
*)

let generateSignature tsName ts = match ts with TypedLanguage(signatureTypes,signatureTerms,rules) ->
generateSigPreamble tsName ^ (String.concat "\n" (List.map generateTypeEntry signatureTypes)) ^ "\n" ^ (String.concat "\n" (List.map generateTermEntry signatureTerms))  ^ "\n\n" ^ extraSigForPredicates

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

let generateModule tsName ts = match ts with TypedLanguage(signatureTypes,signatureTerms,rules) -> generateModPreamble tsName ^ (String.concat "\n" (List.map generateRule rules))

let rec generateTactic tactic = match tactic with 
 | Intros(hyps) -> "intros " ^ (String.concat " " hyps) ^ "."
 | Case(hyp) -> "case " ^ hyp ^ "."
 | CaseKeep(hyp) -> "case " ^ hyp ^ "(keep)."
 | Induction(n) -> "induction on " ^ (string_of_int n) ^ "."
 | Backchain(lemma, name) -> "backchain " ^ lemma ^ "_" ^ name ^ "."
 | Apply(lemma,hyps) -> "apply " ^ lemma ^ " to " ^ (String.concat " " hyps) ^ "."
 | Assert(formula) -> "assert (" ^ formula ^ ")."
 | Inst(hyp, term) -> "inst " ^ hyp ^ " with n1 = " ^ term ^ "."
 | InstAndCut(hyp1,term,hyp2) -> generateTactic (Named("ToCut", Inst(hyp1, term))) ^ " cut ToCut with " ^ hyp2 ^ "." 
 | Search -> "search."
 | Named(hyp,tactic) -> hyp ^ " : " ^ generateTactic tactic

 let rec generateProof proof = match proof with 
| Qed -> ""
| Tactic(tactic) -> generateTactic tactic
| Seq(proofs) -> String.concat " " (List.map generateProof proofs) ^ "\n"
| Repeat(n, hyp, pr) -> generateProof (ForEach((getFormalVariables hyp n), pr))
| ForEach(hyps, pr) -> String.concat " " (List.map generateProof (List.map (substituteXinProof pr) hyps))
| RepeatPlain(n, pr) ->   String.concat " " (Array.to_list (Array.make n (generateProof pr)))

let rec generateTheorem theorem = match theorem with Theorem(statement, proof) -> statement ^ "\n" ^ generateProof proof
let rec generateTheoremS theorems = String.concat "\n\n" (List.map generateTheorem theorems)

let generateAbellaQuery rule = 
	let variablesInConclusion = formula_getAllVariables (rule_getConclusion rule) in 
	let removedVacuousApplications = List.filter (fun premise -> not(term_isApplication (formula_getFirstInput premise)) || List.for_all (fun x -> List.mem x variablesInConclusion) (term_getVariables (formula_getFirstInput premise))) (rule_getPremises rule) in 
    let allVariables = variablesInConclusion @ List.concat (List.map formula_getAllVariables removedVacuousApplications) in
    let forallPreamble = if allVariables = [] then "" else "forall " ^ (String.concat " " (List.unique (List.map toString allVariables))) ^ ", " in 
	let testname = rule_getRuleName rule in 
    let displayedPremises = List.map generateFormula removedVacuousApplications in
    let wrappedInBrackets = fun formula -> "{" ^ formula ^ "}" in
	let implications = if displayedPremises = [] then "" else String.concat " -> " (List.map wrappedInBrackets displayedPremises) ^ " -> " in 
        "Define " ^ testname ^ " : prop by\n   " ^ testname ^ " := " ^ forallPreamble ^ implications ^ wrappedInBrackets (generateFormula (rule_getConclusion rule)) ^ ".\n\n"

