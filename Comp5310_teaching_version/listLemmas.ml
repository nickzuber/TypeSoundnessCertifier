
open Aux
open TypedLanguage
open Ldl
open Proof 
open ListManagement
open GenerateLambdaProlog
open Subtyping


let theoremUpdateAndMember typeDecl = 
	let typeOperator = (type_getOperator typeDecl) in 
	let c = (chop_last_char typeOperator 'T') in 
	let theoremForth = "Theorem " ^ updateSynchLemma c ^ " : forall List L E1 E2, {" ^ termListMember c ^ " List L E1} ->  exists List', {" ^ termListUpdate c ^ " List L E2 List'}. \n"  in 
	let theoremBack = "Theorem " ^ updateSynchLemma c ^ "_back : forall List List' L E1, {" ^ termListUpdate c ^ " List L E1 List'} ->  exists E2, {" ^ termListMember c ^ " List L E2}. \n"  in 
	let withInstruction forthFlag =  if forthFlag then " with E2 = E2." else "." in 
	let proof forthFlag = "induction on 1. intros Main. Hyp : case Main. \n"
				^ "search. \n"
				^ "apply IH to Hyp" ^ withInstruction forthFlag ^ " search.\n "
			in [Theorem(theoremForth ^ proof true, Qed) ; Theorem(theoremBack ^ proof false, Qed)]
			

let listWidthLemma typeDecl = 
	let typeOperator = (type_getOperator typeDecl) in 
	let c = (chop_last_char typeOperator 'T') in 
	let inversionlemmaname = inversion_subtype_NAME ^ "_" ^ typeOperator in 
	let conclusion = if list_isInvariant typeDecl then "{" ^ typeListMember c ^ " List1 L T}. \n" else "exists T2, {" ^ typeListMember c ^ " List1 L T2} /\\ {subtype T2 T}. \n" in 
	let theorem = "Theorem " ^ list_width typeOperator ^ ": forall List1 List2 L T, {" ^ typeListMember c ^ " List2 L T} -> {subtype (" ^ c ^ "T List1) (" ^ c ^ "T List2)} -> " ^ conclusion in 
    let invertedAssumptionToPoke = if list_isInvariant typeDecl then "InvertedAssumption1" else "InvertedAssumption2" in 
	let proof = "induction on 1. intros Main Subtype. case Main. \n"
  			 ^ "Cases : apply " ^ inversionlemmaname ^ " to Subtype. case Cases. search. \n"
  		  	 ^ "Cases : apply " ^ inversionlemmaname ^ " to Subtype. InvertedAssumption1 : case Cases. "
			 ^ "apply IH to H1 " ^ invertedAssumptionToPoke ^ ". search. \n" in (* the last one was H5 *)
			 [Theorem(theorem ^ proof, Qed)]
			 
let listSynchLemma typeDecl = 
	let typeOperator = (type_getOperator typeDecl) in 
	let c = (chop_last_char typeOperator 'T') in 
	let inversionlemmaname = inversion_subtype_NAME ^ "_" ^ typeOperator in 
	let widthlemmaname = list_width typeOperator in 
	let mainTyping = Formula(typing, [Constructor(c, [Var "List1"])], [Constructor(c ^ "T", [Var "List2"])]) in 
	let typeMember = Formula(typeListMember c, [Var "List2" ; Var "L" ; Var "T"], []) in 
	let termMember = Formula(termListMember c, [Var "List1" ; Var "L" ; Var "E"], []) in 
	(*let varToCheck = if typeDecl_isSelfList typeDecl then (Application(Var "E", Constructor(c, [Var "List1"]))) else Var "E" in 
	let typeOutput = Formula(typing, [varToCheck], [Var "T"]) in 
    let invertedAssumptionToPoke = if list_isInvariant typeDecl then "InvertedAssumption1" else "InvertedAssumption2" in *)
	let preambleTheoremSynch = "Theorem " ^ memberSynchLemma (c ^ "T") ^ " : forall List1 List2 L T, " ^ wrappedInBrackets (generateFormula mainTyping) ^ " -> " in 
	let theoremSynchSchema preamble = 
			preamble
			^ wrappedInBrackets (generateFormula typeMember) ^ " -> "
			^ " exists E, "
			^ wrappedInBrackets (generateFormula termMember) 
			(*
			^ " /\\ "
			^ wrappedInBrackets (generateFormula typeOutput) 
			*)
			^ ". \n"
		in 
    let inductionAndCaseAnalysis = "induction on 1. intros TypeOf Member. TypeOfList1 : case TypeOf. \n" in 
    let subsumptionCase = 
      "Cases : apply " ^ inversionlemmaname ^ " to TypeOfList2. InvertedAssumption1 : case Cases.  \n"
    ^ "  case Member.  \n"
    ^ " Width : apply " ^ widthlemmaname ^ " to Member TypeOfList2.  \n" 
    ^ " apply IH to TypeOfList1 Width. \n" (* the last one was H8 *)
    ^ " search.  \n"
  	 in 
	let emptyAndConsCases = "case Member.  \n" ^ "case Member. search. apply IH to TypeOfList2 H1. search.  \n" in 
	let proofSynch = (inductionAndCaseAnalysis
					  ^ (if typeDecl_isSelfList typeDecl 
						  then  (* 1 case before subsumption: the call to typeOfWithSelf, so we call the dedicated lemma for it.  *)
						  		"backchain " ^ memberSynchLemmaForSelf (c ^ "T") ^ ".\n"
						  else  (* 2 cases before subsumption: empty and cons *)
						 	 	emptyAndConsCases)
					  ^ subsumptionCase) in 
	let theoremSynchForSelf = if typeDecl_isSelfList typeDecl 
			then let mainTypeWithSelf = Formula(typeOfWithSelf, [Constructor(c ^ "T", [Var "Whole"]) ; Constructor(c, [Var "List1"])], [Constructor(c ^ "T", [Var "List2"])]) in 
				 let preambleTheoremSelf  =  "Theorem " ^ memberSynchLemmaForSelf (c ^ "T") ^ " : forall Whole List1 List2 L T, " 
				 ^ wrappedInBrackets (generateFormula mainTypeWithSelf) ^ " -> "
			 		in [Theorem(theoremSynchSchema preambleTheoremSelf ^ inductionAndCaseAnalysis ^ emptyAndConsCases, Qed)]
			else [] in 
	  listWidthLemma typeDecl @ theoremSynchForSelf @ [Theorem(theoremSynchSchema preambleTheoremSynch ^ proofSynch, Qed)] @ theoremUpdateAndMember typeDecl

let list_unique_label memberPred cons = 
 	let theorem = "Theorem " ^ unique_lemma memberPred ^ " : forall L E E1 E2 Rest, {" ^ memberPred ^ " (" ^ cons ^ " L E Rest) L E1} -> {" ^ memberPred ^ " Rest L E2} -> false. skip.\n" in 
 	[Theorem(theorem, Qed)]

let listPreserveLemma typeDecl = 
	let typeOperator = (type_getOperator typeDecl) in 
	let c = (chop_last_char typeOperator 'T') in 
	let inversionlemmaname = inversion_subtype_NAME ^ "_" ^ typeOperator in 
	let widthlemmaname = list_width typeOperator in 
	let mainTyping = Formula(typing, [Constructor(c, [Var "List1"])], [Constructor(c ^ "T", [Var "List2"])]) in 
	let typeMember = Formula(typeListMember c, [Var "List2" ; Var "L" ; Var "T"], []) in 
	let termMember = Formula(termListMember c, [Var "List1" ; Var "L" ; Var "E"], []) in 
	let varToCheck = if typeDecl_isSelfList typeDecl then (Application(Var "E", Constructor(c, [Var "List1"]))) else Var "E" in 
	let typeOutput = Formula(typing, [varToCheck], [Var "T"]) in 
	let preamble = "Theorem " ^ c ^ "_" ^ memberPreservationLemma ^ " : forall List1 List2 L T E, " ^ wrappedInBrackets (generateFormula mainTyping) ^ " -> " in 
	let theoremPreserve preamble conclusion = 
			preamble 
			^ wrappedInBrackets (generateFormula typeMember) ^ " -> "
			^ wrappedInBrackets (generateFormula termMember) ^ " -> "
			^ wrappedInBrackets (generateFormula conclusion) ^ ". \n" in 
	let inductionAndCaseAnalysis = "induction on 1. intros TypeOf Member1 Member2. TypeOf1 : case TypeOf(keep).  \n" in 
	let subsumptionCase = 
		  " Cases : apply " ^ inversionlemmaname ^ " to TypeOf2. InvertedAssumptions1 : case Cases. case Member1.  \n"
		  ^ " Width : apply " ^ widthlemmaname ^ " to Member1 TypeOf2. \n"
		  ^ " apply IH to TypeOf1 Width Member2. \n" (* the middle one was H8 *)
		  ^ " search.  \n"
	  in 
	let emptyAndConsCases isSelfListFlag = 
		" case Member1.  \n\n"
  	  	^ " Member1_1 : case Member1(keep). \n"
  	  	^ " Member2_1 : case Member2(keep). \n"
		^ (if isSelfListFlag then "Inst : inst TypeOf1 with n1 = WholeTerm. cut Inst with Whole. " else "")
		^ " search.  \n"
	    ^ " apply " ^ unique_lemma (termListMember c) ^ " to Member2 Member2_1. \n"
	    ^ " Member2_1 : case Member2(keep). \n"
	    ^ " apply " ^ unique_lemma (typeListMember c) ^ " to Member1 Member1_1. \n"
	    ^ (if isSelfListFlag then "apply IH to TypeOf2 Whole Member1_1 Member2_1. search. \n" else " apply IH to TypeOf2 Member1_1 Member2_1. search. \n")
		in 
	let proofSynch = (inductionAndCaseAnalysis
					  ^ (if typeDecl_isSelfList typeDecl 
						  then  (* 1 case before subsumption: the call to typeOfWithSelf, so we call the dedicated lemma for it.  *)
						  		"apply " ^ c ^ "_" ^ memberPreserveLemmaForSelf ^ " to TypeOf1 TypeOf Member1 Member2. search.\n"
						  else  (* 2 cases before subsumption: empty and cons *)
						 	 	emptyAndConsCases false)
					  ^ subsumptionCase) in 
  	let theoremPreserveForSelf = if typeDecl_isSelfList typeDecl 
  			then let mainTypeWithSelf = Formula(typeOfWithSelf, [Var "Whole" ; Constructor(c, [Var "List1"])], [Constructor(c ^ "T", [Var "List2"])]) in 
				 let secondType = Formula(typing, [Var "WholeTerm"], [Var "Whole"]) in 
				 let conclusion = Formula(typing, [(Application(Var "E", Var "WholeTerm"))], [Var "T"]) in 
				 let inductionAndCaseForSelf = "induction on 1. intros TypeOf Whole Member1 Member2. TypeOf1 : case TypeOf. \n" in 
  				 let preambleTheoremSelf  =  "Theorem " ^ c ^ "_" ^ memberPreserveLemmaForSelf ^ " : forall Whole WholeTerm List1 List2 L T E, " 
  				 							 ^ wrappedInBrackets (generateFormula mainTypeWithSelf) ^ " -> " 
										     ^ wrappedInBrackets (generateFormula secondType) ^ " -> "  
  			 		in [Theorem(theoremPreserve preambleTheoremSelf conclusion ^ inductionAndCaseForSelf ^ emptyAndConsCases true, Qed)]
  			else [] in 
  	 list_unique_label (termListMember c) (consList c) @ list_unique_label (typeListMember c) (consListT c) @ theoremPreserveForSelf @ [Theorem(theoremPreserve preamble typeOutput ^ proofSynch, Qed)]

let listPreserveLemmaUpdate typeDecl = 
	let typeOperator = (type_getOperator typeDecl) in 
	let c = (chop_last_char typeOperator 'T') in 
	let inversionlemmaname = inversion_subtype_NAME ^ "_" ^ typeOperator in 
	let widthlemmaname = list_width typeOperator in 
	let mainTyping = Formula(typing, [Constructor(c, [Var "List1"])], [Constructor(c ^ "T", [Var "List"])]) in 
	let typeMember = Formula(typeListMember c, [Var "List" ; Var "L" ; Var "T"], []) in 
	let termUpdate = Formula(termListUpdate c, [Var "List1" ; Var "L" ; Var "E" ; Var "List2"], []) in 
	let typeE = Formula(typing, [ Var "E"], [Var "T"]) in 
	let typeOutput = Formula(typing, [Constructor(c, [Var "List2"])], [Constructor(c ^ "T", [Var "List"])]) in 
	let theoremPreserveUpdate = 
			"Theorem " ^ c ^ "_" ^ updatePreservationLemma ^ " : forall List1 List L T E List2, " 
			^ wrappedInBrackets (generateFormula mainTyping) ^ " -> "			
			^ wrappedInBrackets (generateFormula typeMember) ^ " -> "
			^ wrappedInBrackets (generateFormula termUpdate) ^ " -> "
			^ wrappedInBrackets (generateFormula typeE) ^ " -> "
			^ wrappedInBrackets (generateFormula typeOutput) ^ ". \n" in 
	let inductionAndCaseAnalysis = "induction on 1. intros TypeOf Member1 Update1 TypeE2. TypeOf1 : case TypeOf(keep). \n" in 
	let subsumptionCase = 
		  " Cases : apply " ^ inversionlemmaname ^ " to TypeOf2. InvertedAssumptions1 : case Cases. case Member1.  \n"
		  ^ " Width : apply " ^ widthlemmaname ^ " to Member1 TypeOf2. \n"
		  ^ " apply IH to TypeOf1 Width Update1 TypeE2. \n" (* the middle one was H8 *)
		  ^ " search.  \n"
	  in 
	let emptyAndConsCases = 
		" case Member1.  \n\n"
  	  	^ " Member2 : case Member1(keep). \n"
  	  	^ " Update2 : case Update1(keep). \n"
		^ " search.  \n"
		^ " Member2 : apply " ^ updateSynchLemma c ^ "_back to Update1. \n "
		^ " Member2_1 : apply " ^ updateSynchLemma c ^ "_back to Update2. \n "
	    ^ " apply " ^ unique_lemma (termListMember c) ^ " to Member2 Member2_1. \n"
	    ^ " Update2 : case Update1(keep). \n"
	    ^ " apply " ^ unique_lemma (typeListMember c) ^ " to Member1 Member2. \n"
	    ^ " apply IH to TypeOf2 Member2 Update2 TypeE2. search. \n"
		in 
		let proof = inductionAndCaseAnalysis ^ emptyAndConsCases ^ subsumptionCase in 
  	      [Theorem(theoremPreserveUpdate ^ proof, Qed)]


let listPreservationLemmas typeDecl = listPreserveLemma typeDecl @ listPreserveLemmaUpdate typeDecl

(*
let lemmasForLists ldl typeDecl = 
	 [
	 listCasesLemma ldl typeDecl ;
	 listSynchLemma typeDecl ;
	 listPreserveLemma typeDecl 
	 ]
	
*)
