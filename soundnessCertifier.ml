open Batteries
open Enum
open List
open Unix
open Aux
open TypedLanguage
open SafeTypedLanguage
open SafeToTyped
open TypeCheckerTL
open Proof
open Values
open ErrorManagement
open ContextualRules
open ErrorManagement
open CanonicalForms
open Progress
open Preservation
open SafeToTyped
open GenerateLambdaProlog
open PreservationTests
open Parser

let sep = "\n\n"
let generateThm tsName ts = generateThmPreamble tsName ^ sep ^ (generateTheoremS (generateCanonicalFormsLemma ts)) ^ sep ^ (progressDefinition ts) ^ sep ^ (generateTheoremS (generateProgressLemmas ts)) ^ sep ^ (generateTheorem (generateProgressTheorem ts)) ^ sep ^ (generateTheorem (generatePreservationTheorem ts)) ^ sep ^ typesoundnessProof 

let checkResult tlName output = 
	if String.exists (last output) "Abella < Goodbye." 
		then ()
		else print_string ("FAILED Type Preservation. Specification: " ^ tlName ^ ". Rule: " ^ String.tail (fst (String.split (last output) "<")) (String.length "test_") ^ "\n")
	

let runPreservationTests tlName sl = 
	let test_thm = open_out ("./generated/test_" ^ tlName ^ ".thm") in 
		output_string test_thm ("Specification \"" ^ tlName ^ "\".\n\n");
		List.map (output_string test_thm) (List.map generateAbellaQuery (preservationTestsAsRules sl));
		close_out test_thm;
		let directory = getcwd () in 
			chdir "generated"; 
			let output = callAbella ("abella test_" ^ tlName ^ ".thm") in 
				chdir directory;
				checkResult tlName output;; 

				  
let tlTable = [
(* CBN Calculi *)
"stlc_cbn" ; 
"stlc_cbv" ; 
"stlc_par" ; 
"pairs_superlazy" ; 
"pairs_lazy" ; 
"pairs_plain" ; 
"pairs_onlyfstButBoth" ; 
"iff" ;
"lists" ;
"lists_lazy" ;
"listsIsNil";
"listsIsNil_lazy" ;
"sums" ;
"unitt" ;
"itlc_cbn" ;
"itlc_cbv" ;
"itlc_par" ;
"tuples_lazy" ;
"tuples_parallel" ;
"tuples_plain" ;
"foralll" ;
"recursive" ;
(* STLC with if and booleans *)
"stlc_cbn_iff" ;
"stlc_cbn_iff_par" ;
"stlc_cbv_iff" ;
"stlc_cbv_iff_par" ;
"stlc_par_iff" ;
"stlc_par_iff_par" ;
(* STLC with pairs lazy, superlazy etcetera *)
"stlc_cbn_pairs_lazy" ;
"stlc_cbn_pairs_superlazy" ;
"stlc_cbn_pairs_plain" ;
"stlc_cbn_pairs_onlyfstButBoth" ;
"stlc_cbn_pairs_onlysnd" ;
"stlc_cbv_pairs_lazy" ;
"stlc_cbv_pairs_superlazy" ;
"stlc_cbv_pairs_plain" ;
"stlc_cbv_pairs_onlyfstButBoth" ;
"stlc_cbv_pairs_onlysnd" ;
"stlc_par_pairs_lazy" ;
"stlc_par_pairs_superlazy" ;
"stlc_par_pairs_plain" ;
"stlc_par_pairs_onlyfstButBoth" ;
"stlc_par_pairs_onlysnd" ;
(* STLC with lists *)
"stlc_cbn_lists" ;
"stlc_cbn_lists_lazy" ;
"stlc_cbv_lists" ;
"stlc_cbv_lists_lazy" ;
"stlc_par_lists" ;
"stlc_par_lists_lazy" ;
(* STLC with lists with booleans and isNil *)
"stlc_cbn_listsIsNil" ;
"stlc_cbn_listsIsNil_lazy" ;
"stlc_cbv_listsIsNil" ;
"stlc_cbv_listsIsNil_lazy" ;
"stlc_par_listsIsNil" ;
"stlc_par_listsIsNil_lazy" ;
(* STLC with fix *)
"stlc_cbn_fix" ;
"stlc_cbv_fix" ;
"stlc_par_fix" ;
(* Implicitly Typed Lambda Calculus with fix *)
"itlc_cbn_fix" ;
"itlc_cbv_fix" ;
"itlc_par_fix" ;
(* STLC with let *)
"stlc_cbn_let" ;
"stlc_cbv_let" ;
"stlc_par_let" ;
(* STLC with letrec with type annotations *)
"stlc_cbn_letrecWithType" ;
"stlc_cbv_letrecWithType" ;
"stlc_par_letrecWithType" ;
(* Implicitly Typed Lambda Calculus with letrec with no type annotations *)
"itlc_cbn_letrec" ;
"itlc_cbv_letrec" ;
"itlc_par_letrec" ;
(* Implicitly Typed Lambda Calculus with letrec with no type annotations *)
"itlc_cbn_letrecFix" ;
"itlc_cbv_letrecFix" ;
"itlc_par_letrecFix" ;
(* STLC with sums *)
"stlc_cbn_sums" ;
"stlc_cbv_sums" ;
"stlc_par_sums" ;
(* STLC with unit *)
"stlc_cbn_unitt" ;
"stlc_cbv_unitt" ;
"stlc_par_unitt" ;
(* STLC with exceptions *)
"stlc_cbn_exc" ;
"stlc_cbv_exc" ;
"stlc_par_exc" ;
(* STLC with tuples lazy, parallel and plain *)
"stlc_cbn_tuples_lazy" ;
"stlc_cbn_tuples_parallel" ;
"stlc_cbn_tuples_plain" ;
"stlc_cbv_tuples_lazy" ;
"stlc_cbv_tuples_parallel" ;
"stlc_cbv_tuples_plain" ;
"stlc_par_tuples_lazy" ;
"stlc_par_tuples_parallel" ;
"stlc_par_tuples_plain" ;
(* System F *)
"stlc_cbn_forall" ;
"stlc_cbv_forall" ;
"stlc_par_forall" ;
(* LambdaFull *)
"fullFledgedWithType_cbn" ;
"fullFledgedWithType_cbv" ;
"fullFledgedWithType_par" ;
(* FullFledged Language: System F with if-then-else and booleans, lists, exceptions and letrec *)
"lambdafull_cbn" ;
"lambdafull_cbv" ;
"lambdafull_par" ;
(* FullFledged Language: System F with implicitly typed abstraction, if-then-else and booleans, lists, exceptions and letrec with no type annotations*)
"fullFledged_cbn" ;
"fullFledged_cbv" ;
"fullFledged_par" ;
]

let testOne tlName =
	let tlRaw = parseFile tlName in 
	let sl = typecheck_tl tlRaw in 
	let tl = compile sl in 
	let mycalculus_sig = open_out ("./generated/" ^ tlName ^ ".sig") in
	let mycalculus_mod = open_out ("./generated/" ^ tlName ^ ".mod") in
	let mycalculus_thm = open_out ("./generated/" ^ tlName ^ ".thm") in
 	output_string mycalculus_sig (generateSignature tlName tl);
    output_string mycalculus_mod (generateModule tlName tl);
	output_string mycalculus_thm (generateThm tlName sl); 
    close_out mycalculus_sig;
    close_out mycalculus_mod;
    close_out mycalculus_thm;
	runPreservationTests tlName sl; 
	let directory = getcwd () in 
		chdir "generated";
		Unix.open_process_in ("abella " ^ (tlName ^ ".thm") ^ " > " ^ (tlName ^ "_output.txt"));
		chdir directory;;


let test () = List.map testOne tlTable

