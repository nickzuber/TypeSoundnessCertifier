
open Type_system
open Aux
open Terms
open Proof
open Batteries

let dynamicSemantics = "step"

let rec toString term = match term with 
  | Var(name) -> name
  | Constructor(name, arguments) -> name ^ " " ^ String.concat " " (List.map toString arguments)

let progressDefinition = "Define progresses : term -> prop by\n\t progresses E := {value E} ;\n\t progresses E := exists E', {" ^ dynamicSemantics ^ " E E'}."

let appealToCanonicalForm progressingArguments argToInstanciate c signatureTypes signatureTerms destructed =
         let terms =  List.map (formalTermByConstructor signatureTerms) destructed in 
         let typeBeingDestructed =  destructedTypeBy c signatureTypes in 
         let arguments = fun term -> String.concat " " (List.map toString (getArgumentsOfConstructor term)) in 
         let transformation = fun term -> if (getArgumentsOfConstructor term) = [] then argToInstanciate ^ " = " ^ (toString term) else "exists " ^ (arguments term) ^ ", " ^ argToInstanciate ^ " = " ^ (toString term) in
		  appendProof (createSeq [Named("Canonical", Assert(String.concat " \\/ " (List.map transformation terms))) ; Backchain("canonical_form", typeBeingDestructed) ; Case("Canonical")]) (RepeatPlain(List.length terms, Tactic(Search)))

let progressLemmasForEachConstructor signatureTypes signatureTerms term = 
         let extract = fun arguments -> fun n -> List.nth arguments n in
         let constructor = (getConstructor term) in 
         let argumentsAsList =  (List.map toString (getArgumentsOfConstructor term)) in 
         let (formalTerms,b,c) = (getTermsAndTheRestByConstructor constructor signatureTerms) in 
		 let ctxIndexes = getContextualIndexesByConstructor constructor signatureTerms in 
		 let progressingArguments = List.map (List.nth (List.take (List.length formalTerms) argumentsAsList)) ctxIndexes in
         let arguments = if argumentsAsList = [] then "" else " " ^ String.concat " " argumentsAsList in
         let toImplications = (fun var -> "progresses " ^ var ^ " -> ") in
         let progresses = String.concat "" (List.map toImplications progressingArguments) in
         let finalprogress = "progresses (" ^ constructor ^ arguments ^ ")." in
         let theorem = "Theorem progress_" ^ constructor ^ " : forall" ^ arguments ^ " T, {typeOf (" ^ constructor ^ arguments ^ ") T} -> " ^ progresses ^ finalprogress in
         let caseForProgresses = (fun name -> "case " ^ name ^ ". ") in
         let searches = (fun name -> "search.") in
         let preamble = Seq([Tactic(Intros(["Main" ; arguments])) ; Tactic(Case("Main")) ; ForEach(progressingArguments, Tactic(Case("x")))])  in 
         let proof = if (isTypeConstructor signatureTypes constructor) then RepeatPlain((List.length progressingArguments) + 1, Tactic(Search)) (* I had to add one more search *)
                           else Seq(appealToCanonicalForm progressingArguments (List.hd argumentsAsList) constructor signatureTypes signatureTerms (destructedTermsBy signatureTypes constructor)) @ [(RepeatPlain((List.length progressingArguments), Tactic(Search)))] in 
                  Theorem(theorem, Seq([preamble ; proof]))

(* returns progressDef, (theorem, proof) list *)
let generateProgressLemmas ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let typingRules = List.filter onlyTypingRules rules in
         let formalTerms = (List.map getTermInInput (List.map getConclusion typingRules)) in       
          (List.map (progressLemmasForEachConstructor signatureTypes signatureTerms) formalTerms)

let generateProgressTheorem ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) ->
         let theorem = "Theorem progress : forall E T, {typeOf E T} -> progresses E. \ninduction on 1. intros Main. E1 : case Main." in
         let onlyOfTypeTerm = (fun termconstructor -> match termconstructor with (c, arity) -> let (a,b,rest) = (getTermsAndTheRestByConstructor c signatureTerms) in (c, List.length a)) in 
         let termconstructors = List.map onlyOfTypeTerm (List.map getConstructorAndArityForOperator signatureTerms) in
         let proofBycases = (fun termconstructor -> match termconstructor with (c, arity) -> if arity = 0 then Tactic(Search) else Seq([Repeat(arity, "E", createSeq [Apply("IH", ["x"])]) ; Tactic(Backchain("progress", c))])) in
         let proof = Seq(List.map proofBycases termconstructors) in
          Theorem(theorem, proof)
