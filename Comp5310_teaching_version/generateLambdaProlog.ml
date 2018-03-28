
open Batteries
open Aux
open TypedLanguage
open Ldl
open Proof
open ListManagement

let extraSigForPredicates =
"type value term -> o.\n
type error term -> o.\n
type typeOf term -> typ -> o.\n
type step term -> term -> o.\n
type nstep term -> term -> o.\n\n"

let generateSigPreamble tsName = "sig " ^ tsName ^ ".\n\nkind term type.\nkind typ type.\n\n"
let generateSigPreambleFROM_LAN tsName = "sig " ^ tsName ^ ".\n\nkind term type.\nkind typ type.\n\n" ^ extraSigForPredicates
let generateModPreamble tsName = "module " ^ tsName ^ ".\n\n"
let generateThmPreamble tsName = "Specification \"" ^ tsName ^ "\".\n\n"

let wrappedInBrackets formulaString = "{" ^ formulaString ^ "}" 

let generateKindDeclaration entry = "kind " ^ entry_toKindProduced entry ^ " type.\n"

let generateTypeExpr te = match te with 
         | Simple(variance, typ) -> typ 
         | Abstraction(variance, (typ1,typ2)) -> "(" ^ typ1 ^ " -> " ^ typ2 ^ ")"
         | List(_,c,trm) -> typeList c
         | ListSelf(_,c,trm) -> typeList c

let generateTypeExpr_forLists termDecl = match termDecl with DeclTrm(c,info,ctx,arguments) ->
	let entries = (termEntry_list_getElements (List.hd arguments)) in 
	let entryForTheTerm = if termDecl_isSelfList termDecl then "(term -> term)" else "term" in 
	let typeOfWithSelf = if termDecl_isSelfList termDecl then "type " ^ typeOfWithSelf ^ " typ -> term -> typ -> o.\n" else "" in 
"kind " ^ termList c ^ " type.\n"
^ "kind " ^ typeList c ^ " type.\n\n"
^ "type " ^ emptyList c ^ " " ^ termList c ^ ".\n"
^
"type " ^ consList c ^ " label -> " ^ entryForTheTerm ^ " -> " ^ termList c ^ " -> " ^ termList c ^ ".\n"
^
"type " ^ emptyListT c ^ " " ^ typeList c ^ ".\n"
^
"type " ^ consListT c ^ " label -> typ -> " ^ typeList c ^ " -> " ^ typeList c ^ ".\n\n"
^ 
"type " ^ termListMember c ^ " " ^ termList c ^ " -> label -> " ^ entryForTheTerm ^ " -> o.\n"
^ 
"type " ^ typeListMember c ^ " " ^ typeList c ^ " -> label -> typ -> o.\n"
^ 
"type " ^ termListUpdate c ^ " " ^ termList c ^ " -> label -> " ^ entryForTheTerm ^ " -> " ^ termList c ^ " -> o.\n"
^ typeOfWithSelf
			 
let generateTypeEntry signatureEntry = match signatureEntry with DeclType(c,arguments) ->
let displayArguments = if List.length arguments = 0 then "" else (String.concat " -> " (List.map generateTypeExpr arguments)) ^ " -> " in
"type " ^ c ^ " " ^ displayArguments ^ "typ."

let generateTermEntry signatureEntry = match signatureEntry with DeclTrm(c,info,ctx,arguments) ->
	if List.length arguments = 0 
		then "type " ^ c ^ " term." 
		else if typeEntry_isList (List.hd arguments) 
			then "type " ^ c ^ " " ^ termList c ^ " -> term.\n" (* ^ "type " ^ c ^ "T -> " ^ typeList c ^ " -> term." *)
			else let displayArguments = (String.concat " -> " (List.map generateTypeExpr arguments)) ^ " -> " in "type " ^ c ^ " " ^ displayArguments ^ "term."

let auxiliaryForLists signatureTerms = 
	"kind label type."
    ^ (String.concat "\n" (List.map generateTypeExpr_forLists (List.filter termDecl_isList signatureTerms)))
	
let generateSignature tsName ts = match ts with TypedLanguage(signatureTypes,signatureTerms,rules) ->
	generateSigPreamble tsName 
	^ auxiliaryForLists signatureTerms
	^ (String.concat "\n" (List.map generateTypeEntry signatureTypes)) ^ "\n" 
	^ (String.concat "\n" (List.map generateTermEntry signatureTerms))  ^ "\n\n" 
	^ extraSigForPredicates

let rec generateTerm term = match term with
         | Var(variable) -> variable
         | Constructor(name, arguments) -> "(" ^ name ^ " " ^ (String.concat " " (List.map generateTerm arguments)) ^ ")"
         | Application(term1, term2) -> generateTerm (Constructor(toString term1, [term2]))
         | Bound(variable) -> variable

let rec generateFormula formula = match formula with 
         | Formula(pred, inputs, outputs) ->
                  let argAll = (List.map generateTerm inputs) @ (List.map generateTerm outputs) in
				  	pred ^ " " ^ (String.concat " " argAll)
         | Hypothetical(formula1, formula2) -> "(pi x\\ " ^ generateFormula formula1 ^ " => " ^ generateFormula formula2 ^ ")"
         | Generic(formula) -> "(pi x\\ " ^ generateFormula formula ^ ")"


let generateRule rule = match rule with Rule(name,premises,conclusion) ->
         let prePremises = List.map generateFormula premises in
         let pr = if prePremises = [] then "" else " :- " ^ (String.concat ", " prePremises) in 
           (generateFormula conclusion) ^ pr ^ ".\n"

let generateRules rules = String.concat "\n" (List.map generateRule (rules))

let nstepDefinition = 		
	[Rule("nstepZERO",
		[],
		 Formula("nstep", [Var("E")], [Var("E")])) ;
	 Rule("nstepN",
	 	[Formula("step", [Var("E1")], [Var("E2")]) ;
		 Formula("nstep", [Var("E2")], [Var("E3")]) ;
		],
	 	 Formula("nstep", [Var("E1")], [Var("E3")])) ;
	]

let subsumptionRule = Rule("subsumption", [Formula("typeOf", [Var("E")], [Var("S")]) ;  Formula("subtype", [Var("S") ; Var("T")], [])], Formula("typeOf", [Var("E")], [Var("T")]))

let generateModuleFromLang tsName rules = 
	generateModPreamble tsName 
	^ String.concat "\n" (List.map generateRule rules) ^ "\n"

let generateModule tsName ts = match ts with TypedLanguage(signatureTypes,signatureTerms,rules) -> 
	generateModPreamble tsName 
	^ (String.concat "\n" (List.map generateRule (rules @ nstepDefinition @ listOperations ts))) ^ "\n"

let rec generateTactic tactic = match tactic with 
 | Intros(hyps) -> "intros " ^ (if hyps = [] then "" else " " ^ (String.concat " " hyps)) ^ "."
 | Case(hyp) -> "case " ^ hyp ^ "."
 | CaseKeep(hyp) -> "case " ^ hyp ^ "(keep)."
 | Induction(n) -> "induction on " ^ (string_of_int n) ^ "."
 | Backchain(lemma, name) -> "backchain " ^ lemma ^ "_" ^ name ^ "."
 | Apply(lemma,hyps) -> "apply " ^ lemma ^ (if hyps = [] then "" else " to " ^ (String.concat " " hyps)) ^ "."
 | Assert(formula) -> "assert (" ^ formula ^ ")."
 | Inst(hyp, term) -> "inst " ^ hyp ^ " with n1 = " ^ term ^ "."
 | InstAndCut(hyp1,term,hyp2) -> generateTactic (Named("ToCut", Inst(hyp1, term))) ^ " cut ToCut with " ^ hyp2 ^ "." 
 | Cut(hyp1,hyp2) -> "cut " ^ hyp1 ^ " with " ^ hyp2 ^ "." 
 | Search -> "search."
 | Named(hyp,tactic) -> hyp ^ " : " ^ generateTactic tactic
 | Clear(hyp) -> "clear " ^ hyp ^ "."

 let rec generateProof proof = match proof with 
| Qed -> ""
| Tactic(tactic) -> generateTactic tactic
| Seq(proofs) -> String.concat " " (List.map generateProof proofs) ^ "\n"
| Repeat(n, hyp, pr) -> generateProof (ForEach((getFormalVariables hyp n), pr))
| ForEach(hyps, pr) -> String.concat " " (List.map generateProof (List.map (substituteXinProof pr) hyps))
| RepeatPlain(n, pr) ->   String.concat " " (Array.to_list (Array.make n (generateProof pr)))

(*
	The proof for type soundness is basically language independent when the other proofs are established.
	Exceptionally, here we simply print out proof code, rather than representing the proof. 
	We could have just as easily represent the proof. 
    Example of representing the proof + compile are extensive in other source files such as progress.ml, preservaion.ml, subtyping.ml, and many others. 
*)

let typesoundnessProof err = 
	let errClause = if err then "\/ {error E'} " else "" in 
	let cases = if err then "search. search. apply preservation to TypeOfEPrime H1. search. " else "search. apply preservation to TypeOfEPrime H1. search." in  
	
"Theorem preservation_nstep : forall Exp Exp' Typ, {typeOf Exp Typ} -> {nstep Exp Exp'} -> {typeOf Exp' Typ}. 
induction on 2. intros. case H2. search. 
apply preservation to H1 H3. apply IH to H5 H4. search. \n\n
Theorem type_soundness : forall E E' T, {typeOf E T} -> {nstep E E'} -> 
({value E'} /\\ {typeOf E' T}) " ^ errClause ^ "\/ exists E'', ({step E' E''} /\\ {typeOf E''  T}).
induction on 2. intros Main NStep. 
TypeOfEPrime : apply preservation_nstep to Main NStep. Step1 : case NStep. 
Progress : apply progress to TypeOfEPrime.
case Progress. " 
^ cases ^
"\nTypeOfE2: apply preservation to Main Step1. backchain IH with E = E2.\n"


let rec generateTheorem theorem = match theorem with Theorem(statement, proof) -> statement ^ "\n" ^ generateProof proof
let rec generateTheoremS theorems = String.concat "\n\n" (List.map generateTheorem theorems) ^ "\n\n" 

let generateAbellaQuery (rule, checks) = 
	let variablesInConclusion = formula_getAllVariables (rule_getConclusion rule) in 
	let removedVacuousApplications = (rule_getPremises rule) in 
    let allVariables = variablesInConclusion @ List.concat (List.map formula_getAllVariables removedVacuousApplications) in
    let forallPreamble = if allVariables = [] then "" else "forall " ^ (String.concat " " (List.unique (List.map toString allVariables))) ^ ", " in 
	let testname = rule_getRuleName rule in 
    let displayedPremises = List.map generateFormula removedVacuousApplications in
	let displayChecks = List.map generateFormula checks in 
	let implications = if displayedPremises = [] then "" else String.concat " -> " (List.map wrappedInBrackets displayedPremises) ^ " -> " in 
        "Theorem " ^ testname ^ " : " ^ forallPreamble ^ implications ^ (String.concat " /\\ " (wrappedInBrackets (generateFormula (rule_getConclusion rule)) :: (List.map wrappedInBrackets displayChecks))) ^ ".\n" ^
		"intros. search.\n"


let rec generateFormulaNoPI formula = match formula with 
         | Formula(pred, inputs, outputs) ->
			 if pred = equality then generateTerm (List.nth inputs 0) ^ " = " ^ generateTerm (List.nth inputs 1) else 
                  let argAll = (List.map generateTerm inputs) @ (List.map generateTerm outputs) in
                     pred ^ " " ^ (String.concat " " argAll)
         | Hypothetical(formula1, formula2) -> generateFormulaNoPI formula1 ^ " => " ^ generateFormulaNoPI formula2
         | Generic(formula) -> generateFormulaNoPI formula

let pop_out_equalities listOfFormulas = let equalities = List.filter (formula_isPredicate equality) listOfFormulas in (list_difference listOfFormulas equalities, equalities)
let generateANDformula listOfFormulas = let (listRemoved, equalities) = pop_out_equalities listOfFormulas in 
	String.concat "" (List.map addAnd (List.map wrappedInBrackets (List.map generateFormulaNoPI listRemoved))) ^ String.concat "" (List.map addAnd (List.map generateFormulaNoPI equalities))
let generateANDformulaBetween listOfFormulas = let (listRemoved, equalities) = pop_out_equalities listOfFormulas in 
	String.concat " /\\ " (List.map wrappedInBrackets (List.map generateFormulaNoPI listRemoved)) ^ String.concat "" (List.map addAnd (List.map generateFormulaNoPI equalities))

let term_existentiallyClosedEquation var termDecl = 
	let (canonical, vars) = term_getCanonicalNoClash termDecl in 
	if vars = [] then var ^ " = " ^ (toString canonical) else let existentials = "exists " ^ String.concat " " (List.map toString vars) ^ ", " in 
	let valueTests = if termDecl_isList termDecl then "" else generateANDformula (List.map toValuePremise  (List.map (nthMinusOne vars) (term_getValPositions termDecl))) in 
	 	"(" ^ existentials ^ var ^ " = " ^ (toString canonical) ^ valueTests ^ ")"

let type_existentiallyClosedEquation var typeDecl = 
	let (canonical, vars) = type_getCanonicalNoClash typeDecl in 
	if vars = [] then var ^ " = " ^ (toString canonical) else let existentials = "exists " ^ String.concat " " (List.map toString vars) ^ ", " in 
	 existentials ^ var ^ " = " ^ (toString canonical)

let apply trm = match String.get (generateTerm trm) 0 with 
	| 'R' -> Application(trm, Var "x")
	| _ -> trm

let grammarLetterToType	term = match term with 
	| (Var "E") -> Simple(Cov, "term")
	| (Var "T") -> Simple(Cov, "typ")
	| (Bound "E") -> Abstraction(Cov, ("term","term"))
	| (Bound "TE") -> Abstraction(Cov, ("typ","term"))
	| (Bound "TT") -> Abstraction(Cov, ("typ","typ"))
	| aa -> raise(Failure ("blabla" ^ generateTerm aa))
	
let termsToSignatureType (Constructor(c,args)) = generateTypeEntry (DeclType(c,List.map grammarLetterToType args))
let termsToSignatureTerm (Constructor(c,args)) = generateTermEntry (DeclTrm(c, [], [], List.map grammarLetterToType args))
let termsToValueRule term = let conclusion = toValuePremise term in Rule(formula_getRuleNameFromConclusion conclusion,removeDuplicates (conclusion_implicitValuePremises conclusion),conclusion)
let termsToErrorRule term = let conclusion = toErrorPremise term in Rule(formula_getRuleNameFromConclusion conclusion,removeDuplicates (conclusion_implicitValuePremises conclusion),conclusion)
