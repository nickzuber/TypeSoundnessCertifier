open Aux
open Type_system

type hypothesis = string
type lemmaName = string

type tactic = 
  | Intros of hypothesis list
  | Case of hypothesis
  | CaseKeep of hypothesis
  | Induction of int
  | Backchain of lemmaName * string
  | Apply of lemmaName * (hypothesis list)
  | Assert of string  
  | Inst of hypothesis * string
  | InstAndCut of hypothesis * string * hypothesis
  | Search
  | Named of hypothesis * tactic

type proof =
  | Qed
  | Tactic of tactic
  | Seq of proof list
  | Repeat of int * hypothesis * proof
  | ForEach of hypothesis list * proof
  | RepeatPlain of int * proof
  

type theorem = Theorem of string * proof

let createSeq tactics = let wrapInTactic = fun tact -> Tactic(tact) in Seq(List.map wrapInTactic tactics)
let appendProof proof1 proof2 = Seq([proof1 ; proof2])  (* to do  *)
let toCaseTactic hypName index = Tactic(Case(hypName ^ (string_of_int index)))

let rec substituteXinTactic tactic hyp = let substitute hyp1 hyp2 = if hyp2 = "x" then hyp1 else hyp2 in 
	match tactic with 
| Case(hyp2) -> if hyp2 = "x" then Case(hyp) else Case(hyp2)
| Apply(lemma,hyps) -> Apply(lemma,List.map (substitute hyp) hyps)
| Named(hyp2,tact2) -> Named(hyp2,substituteXinTactic tact2 hyp)
| other -> other


let rec substituteXinProof pr hyp = let swapped = fun pr -> substituteXinProof pr hyp in
  match pr with 
| Tactic(tactic) -> Tactic(substituteXinTactic tactic hyp)
| Seq(proofs) -> Seq(List.map swapped proofs)
| other -> other


let universalQuantification vars = if vars = [] then "" else "forall " ^ String.concat " " vars ^ ", "

let existentiallyClosedEquation var canonicalTermDecl = 
	let (canonical, vars) = canonicalForTermNoClash canonicalTermDecl in 
	if vars = [] then var ^ " = " ^ (toString canonical) else let existentials = "exists " ^ String.concat " " (List.map toString vars) ^ ", " in 
	 "(" ^ existentials ^ var ^ " = " ^ (toString canonical) ^ ")"

	 (*
let existentiallyClosedEquation var signatureTerms canonicalTermDecl = 
	let (canonical, vars) = canonicalForTerm canonicalTermDecl in 
	let existentials = if vars = [] then "" else "exists " ^ String.concat " " (List.map toStringWith' vars) ^ ", " in 
	 existentials ^ var ^ " = " ^ (toStringWith' canonical) 
	 *)