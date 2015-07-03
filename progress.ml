
open Type_system
open Aux
open Terms
open Batteries

let dynamicSemantics = "step"

let rec toString term = match term with 
  | Var(name) -> name
  | Constructor(name, arguments) -> name ^ " " ^ String.concat " " (List.map toString arguments)

let progressDefinition = "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."

let appealToCanonicalForm progressingArguments argToInstanciate c signatureTypes signatureTerms destructed =
         let terms =  List.map (formalTermByConstructor signatureTerms) destructed in 
         let typeBeingDestructed =  destructedTypeBy c signatureTypes in 
         let searches = (fun term -> "search.") in
         let searches2 = (fun term -> "search.") in
         let arguments = fun term -> String.concat " " (List.map toString (getArgumentsOfConstructor term)) in 
         let transformation = fun term -> if (getArgumentsOfConstructor term) = [] then argToInstanciate ^ " = " ^ (toString term) else "exists " ^ (arguments term) ^ ", " ^ argToInstanciate ^ " = " ^ (toString term) in
         let backchainlemma = "canonical_form_" ^ typeBeingDestructed in
          "\n Canonical : assert (" ^ String.concat " \\/ " (List.map transformation terms) ^ "). backchain " ^ backchainlemma ^ ". case Canonical. " ^ (String.concat " " (List.map searches terms)) ^ "\n"

let progressLemmasForEachConstructor signatureTypes signatureTerms term = 
         let extract = fun arguments -> fun n -> List.nth arguments n in
         let constructor = (getConstructor term) in 
         let argumentsAsList =  (List.map toString (getArgumentsOfConstructor term)) in 
         let (a,b,c) = (getTermsAndTheRestByConstructor constructor signatureTerms) in 
		 let progressingArguments = List.take (List.length a) argumentsAsList in
         let arguments = if argumentsAsList = [] then "" else " " ^ String.concat " " argumentsAsList in
         let toImplications = (fun var -> "progresses " ^ var ^ " -> ") in
         let progresses = String.concat "" (List.map toImplications progressingArguments) in
         let finalprogress = "progresses (" ^ constructor ^ arguments ^ ")." in
         let theorem = "Theorem progress_" ^ constructor ^ " : forall" ^ arguments ^ " T, {typeOf (" ^ constructor ^ arguments ^ ") T} -> " ^ progresses ^ finalprogress in
         let caseForProgresses = (fun name -> "case " ^ name ^ ". ") in
         let searches = (fun name -> "search.") in
         let preamble = "intros Main" ^ arguments ^ ". " ^ "case Main. \n " ^ (String.concat " " (List.map caseForProgresses progressingArguments)) in 
         let proof = if (isTypeConstructor signatureTypes constructor) then (String.concat " " (List.map searches progressingArguments))  ^ "search. \n"  
                           else appealToCanonicalForm progressingArguments (List.hd argumentsAsList) constructor signatureTypes signatureTerms (destructedTermsBy signatureTypes constructor)  ^ " " ^ (String.concat " " (List.map searches progressingArguments)) in 
                  theorem ^ "\n" ^ preamble ^ proof

let generateProgressLemmas ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let typingRules = List.filter onlyTypingRules rules in
         let formalTerms = (List.map getTermInInput (List.map getConclusion typingRules)) in       
          progressDefinition ^ "\n\n" ^ String.concat "\n\n" (List.map (progressLemmasForEachConstructor signatureTypes signatureTerms) formalTerms)

let generateProgressTheorem ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let theorem = "Theorem progress : forall E T, {typeOf E T} -> progresses E. \ninduction on 1. intros Main. E1 : case Main." in
         let onlyOfTypeTerm = (fun termconstructor -> match termconstructor with (c, arity) -> let (a,b,rest) = (getTermsAndTheRestByConstructor c signatureTerms) in (c, List.length a)) in 
         let termconstructors = List.map onlyOfTypeTerm (List.map getConstructorAndArityForOperator signatureTerms) in
         let applyInduction = fun n -> "apply IH to E" ^ (string_of_int n) ^ "." in
         let proofBycases = (fun termconstructor -> match termconstructor with (c, arity) -> if arity = 0 then "\n search." else "\n " ^ (String.concat " " (List.map applyInduction (range 1 arity))) ^ " backchain progress_" ^ c ^ ".") in
         let proof = String.concat "" (List.map proofBycases termconstructors) in
          theorem ^ proof
