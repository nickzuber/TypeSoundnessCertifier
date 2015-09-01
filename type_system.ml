open Aux

let typing = "typeOf"

(* Examples: Simple int  *)
(* Abstraction term term (for (term -> term)) *)
type type_expression = 
  | Simple of string
  | Abstraction of string * string

(* Examples: Decl arrow typ [abs] [app] [Simple term, Simple term]*)
(* abs is the constructor for arrow. [app] is the set of deconstructors *)
type signature_type =
  | DeclType of string * string * string list * string list * type_expression list

type ctx_info =
| Sequential
| Contextual of int list

(* Examples: Decl app term Contextual [1,2] [Simple term, Simple term] where [1,2] are the contextual arguments *)
type signature_term =
  | DeclTrm of string * string * ctx_info * type_expression list

type term =
  | Var of string
  | Constructor of string * term list 
  | Application of term * term 

(* Example: Formula predicateName inputTerms outputTerms *)
type formula =
  | Formula of string * term list * term list
  | Hypothetical of term * term * term
  | Generic of term * term

type rule =
  | Rule of string * formula list * formula

(* Example: TypeSystem signatureForTypes signatureForTerms rules *)
type type_system =
  | TypeSystem of signature_type list * signature_term list * rule list 

let extend ts newrules = match ts with TypeSystem(signatureTypes, signatureTerms, rules) -> TypeSystem(signatureTypes, signatureTerms, List.append rules newrules)  

let getRules ts = match ts with TypeSystem(signatureTypes, signatureTerms, rules) -> rules
let getPremises rule = match rule with Rule(name,premises,conclusion) -> premises
let getConclusion rule = match rule with Rule(name,premises,conclusion) -> conclusion

let turnFormulaTo newpred formula = match formula with Formula(pred, inputs, outputs) -> Formula(newpred, inputs, outputs)
let turnFormulaToByOutput newpred output formula = match formula with Formula(pred, inputs, outputs) -> Formula(newpred, inputs, output::outputs)

let rec toString term = match term with 
  | Var(name) -> name
  | Constructor(name, arguments) -> "(" ^ name ^ " " ^ String.concat " " (List.map toString arguments) ^ ")"
  | Application(term1, term2) -> "(" ^ toString term1 ^ " " ^ toString term2 ^ ")"

let rec toStringWith' term = match term with 
  | Var(name) -> name ^ "'"
  | Constructor(name, arguments) -> name ^ " " ^ String.concat " " (List.map toStringWith' arguments)

let getConstructor term = match term with 
| Constructor(name, arguments) -> name
| other -> raise (Failure ("getConstructor: I did not find a constructed term, but found : " ^ (toString term)))
let getArgumentsOfConstructor term = match term with Constructor(name, arguments) -> arguments

let rec lookupEntryTerms constructor signatureTerms =  match signatureTerms with
                        | [] -> raise (Failure ("lookupEntryTerms: Given a constructor I could not find it in signatureTerms: " ^ constructor))
                        | DeclTrm(c, kind, ctx, arguments)::rest -> if c = constructor then DeclTrm(c, kind, ctx, arguments) else lookupEntryTerms constructor rest

let rec destructedTermsBy signatureTypes constructor =  match signatureTypes with
                        | [] -> raise (Failure ("destructedTermsBy: Given a deconstructor I could not find its corresponding constructor: " ^ constructor))
                        | DeclType(c, kind, constructors, deconstructors, arguments)::rest -> if List.mem constructor deconstructors then constructors else destructedTermsBy rest constructor

let rec destructedTypeBy constructor signatureTypes =  match signatureTypes with
                        | [] -> raise (Failure ("destructedTermsBy: Given a deconstructor I could not find its corresponding constructor: " ^ constructor))
                        | DeclType(c, kind, constructors, deconstructors, arguments)::rest -> if List.mem constructor deconstructors then c else destructedTypeBy constructor rest

let toTerm variable = Var(variable)
let getFormalVariablesAsTerms prefix n = List.map toTerm (getFormalVariables prefix n)

let rec formalTermByConstructor signatureTerms constructor =  match signatureTerms with
                        | [] -> raise (Failure ("formalTermByConstructor: Given a constructor I could not find it in signatureTerms: " ^ constructor))
                        | DeclTrm(c, kind, cxt, arguments)::rest -> if c = constructor then Constructor(c, getFormalVariablesAsTerms "ARG" (List.length arguments)) else formalTermByConstructor rest constructor

let getConstructorInInput formula = match formula with Formula(pred, inputs, outputs) -> getConstructor (List.hd inputs)
let getTermInInput formula = match formula with Formula(pred, inputs, outputs) -> (List.hd inputs)
let getTermInOutput formula = match formula with Formula(pred, inputs, outputs) -> (List.hd outputs)

let getConstructorAndArityForOperator termEntry = match termEntry with DeclTrm(c, kind, ctx, arguments) -> (c, List.length arguments)

let getDeConstructorFromTypeSignature typeSignature = let getForEach = (fun entry -> match entry with DeclType(c,kind,constructors,deconstructors,arguments) -> deconstructors) in
			                        List.concat (List.map getForEach typeSignature)
let getConstructorFromTypeSignature typeSignature = let getForEach = (fun entry -> match entry with DeclType(c,kind,constructors,deconstructors,arguments) -> constructors) in
			                        List.concat (List.map getForEach typeSignature)


let getConstructorFromEntry signatureEntry = match signatureEntry with DeclType(c,kind,constructors,deconstructors,arguments) -> c

let lookupRuleByConstructor constructor rules = let matchingFilter = (fun rule -> match rule with Rule(name,premises,conclusion) -> (getConstructorInInput conclusion = constructor)) in
			                        (List.filter matchingFilter rules)

let extractArityOfDefined formula = match formula with Formula(pred, inputs, outputs) -> match List.hd inputs with Constructor(name, arguments) -> List.length arguments
                        
let rec isTypeConstructor signatureTypes constructor = match signatureTypes with
                        | [] -> false
                        | DeclType(c, kind, constructors, deconstructors, arguments)::rest -> if List.mem constructor constructors then true else isTypeConstructor rest constructor

let isConstructor term = match term with 
  | Constructor(name, arguments) -> true
  | _ -> false


let rec seekPremise pred premises = match premises with
                        | [] -> raise (Failure "seekPremise: Asked for searching for something that was not present in :premises:")
                        | Formula(pred1, inputs, outputs)::rest -> if pred = pred1 then Formula(pred1, inputs, outputs) else seekPremise pred rest

let rec typeOfPremiseForVariable variable rule = match rule with Rule(name,premises,conclusion) -> let checkIfItIsAboutTheVar = fun term -> if term = variable then true else match term with Application(term1, term2) -> term1 = variable in
                        match premises with              
                        | [] -> raise (Failure ("seekPremise: Asked for searching for something that was not present in :premises:" ^ toString variable ^ toString (getTermInInput conclusion)))
                        | Formula(pred1, inputs, outputs)::rest -> if checkIfItIsAboutTheVar (List.hd inputs) then 0 else typeOfPremiseForVariable variable (Rule(name,rest,conclusion))
                        | Hypothetical(typ1, term1, typ2)::rest -> if checkIfItIsAboutTheVar term1 then 1 else typeOfPremiseForVariable variable (Rule(name,rest,conclusion))
                        | Generic(term1, term2)::rest -> if checkIfItIsAboutTheVar term1 then 2 else typeOfPremiseForVariable variable (Rule(name,rest,conclusion))


let rec getNumberOfTerms arguments = match arguments with 
                        | [] -> 0
                        | Simple(typ)::rest -> if typ = "term" then 1 + getNumberOfTerms rest else getNumberOfTerms rest 
                        | Abstraction(typ1,typ2)::rest -> getNumberOfTerms rest

let rec getNumberOfAbstractions arguments = match arguments with 
                        | [] -> 0
                        | Simple(typ)::rest -> getNumberOfAbstractions rest
                        | Abstraction(typ1,typ2)::rest -> 1 + getNumberOfAbstractions rest
						
let rec getNumberOfAbstractionsByConstr constructor signatureTerm = match signatureTerm with 
                        | [] -> raise (Failure "getNumberOfAbstractionsByConstr: Asked for searching for something in signatureTerm that was not present")
                        | DeclTrm(c, kind, ctx, arguments)::rest -> if constructor = c then getNumberOfAbstractions arguments else getNumberOfAbstractionsByConstr constructor rest

let rec getNumberOfSimplesByConstr constructor signatureTerm = let searchForMine = fun pair -> match pair with (c, arity) -> if c = constructor then true else false in
                        let (c, arity) = List.hd (List.filter searchForMine (List.map getConstructorAndArityForOperator signatureTerm)) in 
                         arity - (getNumberOfAbstractionsByConstr constructor signatureTerm)

let rec getAppliedTermsFor abstraction term =  match term with 
  | Var(variable) -> []
  | Constructor(name, arguments) -> List.concat (List.map (getAppliedTermsFor abstraction) arguments)
  | Application(term1, term2) -> if (toString abstraction) = (toString term1) then [term2] else [] 


let getTermsAndTheRest arguments = 
                            let numTerms = getNumberOfTerms arguments in 
                            let numAbstractions = getNumberOfAbstractions arguments in
							let numTheRest = (List.length arguments) - numAbstractions - numTerms in 
                            let formalTerms = Aux.getFormalVariables "E" numTerms in 
                            let formalAbstractions = Aux.getFormalVariables "E" numAbstractions in 
                            let formalTheRest = Aux.getFormalVariables "X" numTheRest in 
                            let createTermForVar = (fun name -> (Var name)) in
                            let numeberedVar = fun newVars -> (List.map createTermForVar newVars) in 
                             ((numeberedVar formalTerms), (numeberedVar formalAbstractions), (numeberedVar formalTheRest))

let getTermsAndTheRestByConstructor constructor signatureTerms = match (lookupEntryTerms constructor signatureTerms) with DeclTrm(c, kind, ctx, arguments) -> getTermsAndTheRest arguments

let getContextualIndexesByConstructor constructor signatureTerms = 
	match (lookupEntryTerms constructor signatureTerms) with DeclTrm(c, kind, ctx, arguments) -> 
		let (formalTerms,b,c) = (getTermsAndTheRestByConstructor constructor signatureTerms) in 
		 match ctx with 
		| Sequential -> Aux.range 0 ((List.length formalTerms) - 1)
		| Contextual(args) -> List.map Aux.decrement args 

let rec getAllVariables_Term term = match term with 
  | Var(name) ->  [Var(name)]
  | Constructor(name, arguments) -> (List.concat (List.map getAllVariables_Term arguments))
  | Application(term1, term2) -> (List.concat (List.map getAllVariables_Term [term1 ; term2]))

let getAllVariables_Formula formula = match formula with Formula(pred, inputs, outputs) -> (List.concat (List.map getAllVariables_Term inputs)) @ (List.concat (List.map getAllVariables_Term outputs))

let getAllVariables rule = match rule with Rule(name,premises,conclusion) -> (List.concat (List.map getAllVariables_Formula premises)) @ (getAllVariables_Formula conclusion)

let rec retrieveApplication term signatureTerms conclusionTerm = match term with Constructor(name, arguments) -> 
         let abstraction = List.hd arguments in 
		 let appliedTerms = getAppliedTermsFor abstraction conclusionTerm in
		 List.hd appliedTerms
		 
		 
let rec deBrujinStyleIndex term1 term2 pair = if term1 = term2 then pair else match pair with (m, n) -> 
	let listForArguments = fun i -> (m+1, i) in 
	let interation = fun call -> match call with (arg, (newm, newn)) -> deBrujinStyleIndex term1 arg (newm, newn) in
	let filterForTheGoodOne = fun pair -> match pair with (m,n) -> (m > -1) in
	let search = (match term2 with 
    | Var(name) -> [(-1, -1)]
    | Constructor(name, arguments) -> (List.map interation (List.combine arguments (List.map listForArguments (range 1 (List.length arguments)))))
    | Application(term1, term2) -> [(-1, -1)]) in 
	let result = (List.filter filterForTheGoodOne search) in if result = [] then (-1, -1) else List.hd result

let rec getRangeOfArgumentsOfTypeTerms constructor signatureTerms = 
	let onlyTerms = fun pair -> match pair with (b, n) -> b in 
	let spotTerms = fun i -> fun entry -> match entry with | Simple("term") -> (true, i) | _ -> (false, i)  in 
		match signatureTerms with 
                        | [] -> raise (Failure "getNumberOfAbstractionsByConstr: Asked for searching for something in signatureTerm that was not present")
                        | DeclTrm(c, kind, ctx, arguments)::rest -> if c = constructor then List.map snd (List.filter onlyTerms (List.mapi spotTerms arguments)) else getRangeOfArgumentsOfTypeTerms constructor rest
