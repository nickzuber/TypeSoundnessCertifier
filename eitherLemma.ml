
open Type_system
open Aux
open Terms
open Proof

let eachSubGoal signatureTerms rule = match rule with Rule(name,premises,conclusion) -> 
         let constructor = getConstructorInInput conclusion in 
         let (formalTerms, formalAbstractions, theRest) = (getTermsAndTheRestByConstructor constructor signatureTerms) in 
		  Seq([Repeat((List.length formalTerms), "TermPred", createSeq [Named("Tmp", Apply("IH", ["x"])) ; Case("Tmp")]) ;
		  								Tactic(Search) ;
										RepeatPlain((List.length formalTerms), Tactic(Search))])

let generateEitherLemma ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> 
         let statement = "Theorem eitherValueOrNot : forall E, {termPred E} -> {value E} \\/ {nonvalue E}." in
		 let preambleproof = createSeq([Induction(1) ; Intros(["Main"]) ; Named("TermPred1", Case("Main"))]) in
         let proof = Seq((List.map (eachSubGoal signatureTerms) (List.filter Terms.onlyTermPredRules rules))) in
          Theorem(statement, appendProof preambleproof proof)
