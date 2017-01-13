open Batteries
open Enum
open List
open Unix
open Aux
open TypedLanguage
open Ldl
open LdlToTypedLanguage
open TypeChecker
open TypeCheckerTypedLanguage
open Proof
open Values
open ErrorManagement
open ContextualRules
open ErrorManagement
open CanonicalForms
open Progress
open Preservation
open TypeSoundness
open LdlToTypedLanguage
open GenerateLambdaProlog
open TypeCheckerPreservation
open Parser


let sep = "\n\n"
let generateThm tsName ldl = generateThmPreamble tsName ^ sep ^ 
							(generateTheoremS (generateCanonicalFormsLemma ldl)) 
							^ sep ^ 
							(progressDefinition ldl) 
							^ sep ^ 
							(generateTheoremS (generateProgressLemmas ldl)) 
							^ sep ^ 
							(generateTheorem (generateProgressTheorem ldl)) 
							^ sep ^
							(generateTheorem (generatePreservationTheorem ldl)) 
							^ sep ^ 
							typesoundnessProof (ldl_containErrors ldl)

							
let checkResult tlName output = 
	if (String.exists (last output) "< search.") 
		(* if Abella 2.0.2, 2.0.3, and 2.0.4 fail our type preservation check, they quit abruptly after "search.", which is then the last line *)
		(* this check above will be replaced with a better way to interact with Abella *)
		then raise(Failure("FAILED Type Preservation. Specification: " ^ tlName ^ ". Rule: " ^ String.tail (fst (String.split (last output) "<")) (String.length "test_") ^ "\n"))
		else ()

let runPreservationTests tlName ldl = 
	let test_thm = open_out ("./generated/test_" ^ tlName ^ ".thm") in 
		output_string test_thm ("Specification \"" ^ tlName ^ "\".\n\n");
		List.map (output_string test_thm) (List.map generateAbellaQuery (preservationTestsAsRules ldl));
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
"pairs_rightToleft" ; 
"pairs_onlyfstButBoth" ; 
"iff" ;
"lists" ;
"lists_lazy" ;
"lists_rightToleft" ;
"listsIsNil";
"listsIsNil_lazy" ;
"listsIsNil_rightToleft" ;
"sums" ;
"unitt" ;
"itlc_cbn" ;
"itlc_cbv" ;
"itlc_par" ;
"tuples_plain" ;
"tuples_lazy" ;
"tuples_parallel" ;
"tuples_rightToleft" ;
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
"stlc_cbn_pairs_rightToleft" ;
"stlc_cbn_pairs_onlyfstButBoth" ;
"stlc_cbn_pairs_onlysnd" ;
"stlc_cbv_pairs_lazy" ;
"stlc_cbv_pairs_superlazy" ;
"stlc_cbv_pairs_plain" ;
"stlc_cbv_pairs_rightToleft" ;
"stlc_cbv_pairs_onlyfstButBoth" ;
"stlc_cbv_pairs_onlysnd" ;
"stlc_par_pairs_lazy" ;
"stlc_par_pairs_superlazy" ;
"stlc_par_pairs_plain" ;
"stlc_par_pairs_rightToleft" ;
"stlc_par_pairs_onlyfstButBoth" ;
"stlc_par_pairs_onlysnd" ;
(* STLC with lists *)
"stlc_cbn_lists" ;
"stlc_cbn_lists_lazy" ;
"stlc_cbn_lists_rightToleft" ;
"stlc_cbv_lists" ;
"stlc_cbv_lists_lazy" ;
"stlc_cbv_lists_rightToleft" ;
"stlc_par_lists" ;
"stlc_par_lists_lazy" ;
"stlc_par_lists_rightToleft" ;
(* STLC with lists with booleans and isNil *)
"stlc_cbn_listsIsNil" ;
"stlc_cbn_listsIsNil_lazy" ;
"stlc_cbn_listsIsNil_rightToleft" ;
"stlc_cbv_listsIsNil" ;
"stlc_cbv_listsIsNil_lazy" ;
"stlc_cbv_listsIsNil_rightToleft" ;
"stlc_par_listsIsNil" ;
"stlc_par_listsIsNil_lazy" ;
"stlc_par_listsIsNil_rightToleft" ;
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
"stlc_cbn_tuples_rightToleft" ;
"stlc_cbv_tuples_lazy" ;
"stlc_cbv_tuples_parallel" ;
"stlc_cbv_tuples_plain" ;
"stlc_cbv_tuples_rightToleft" ;
"stlc_par_tuples_lazy" ;
"stlc_par_tuples_parallel" ;
"stlc_par_tuples_plain" ;
"stlc_par_tuples_rightToleft" ;
(* System F *)
"stlc_cbn_forall" ;
"stlc_cbv_forall" ;
"stlc_par_forall" ;
(* STLC with recursive types *)
"stlc_cbn_recursive" ;
"stlc_cbv_recursive" ;
"stlc_par_recursive" ;
(** Some combinations **)
(* STLC with booleans, lists, sums and letrec *)
"lists_withMore_cbv" ;
"lists_withMore_cbn" ;
"lists_withMore_par" ;
"lists_withMore_rightToleft_cbv" ;
"lists_withMore_rightToleft_cbn" ;
"lists_withMore_rightToleft_par" ;
(* STLC with booleans, lists, sums and letrec *)
"sums_and_pairs_cbv" ;
"sums_and_pairs_cbn" ;
"sums_and_pairs_par" ;
(* STLC with booleans, lists, universal types, fix, let, letrec, and exceptions, with and without type annotations *)
"forall_withMore_cbn" ;
"forall_withMore_cbv" ;
"forall_withMore_par" ;
"forall_withMoreWithType_cbn" ;
"forall_withMoreWithType_cbv" ;
"forall_withMoreWithType_par" ;
(* STLC with booleans, lists, recursive types, fix, letrec, and exceptions, with and without type annotations *)
"recursive_withMore_cbn" ;
"recursive_withMore_cbv" ;
"recursive_withMore_par" ;
(* Paper Fpl: STLC cbv with integers, booleans, pairs, sums, lists, universal types, recursive types, fix, letrec, and exceptions *)
"fpl_cbv"
]

let testOne tlName =
	let tlRaw = parseFile tlName in 
	(try typecheck tlRaw with | Failure errorMessage -> raise(Failure("Typechecker Failure for " ^ tlName ^ ": " ^ errorMessage)));
	let ldl = (try typecheck_tl tlRaw with | Failure errorMessage -> raise(Failure("Failure for " ^ tlName ^ ": " ^ errorMessage))) in 
	let tl = compile ldl in 
	let mycalculus_sig = open_out ("./generated/" ^ tlName ^ ".sig") in
	let mycalculus_mod = open_out ("./generated/" ^ tlName ^ ".mod") in
	let mycalculus_thm = open_out ("./generated/" ^ tlName ^ ".thm") in
 	output_string mycalculus_sig (generateSignature tlName tl);
	output_string mycalculus_mod (generateModule tlName tl);	
	output_string mycalculus_thm (generateThm tlName ldl);
    close_out mycalculus_sig;
    close_out mycalculus_mod;
    close_out mycalculus_thm;	
	runPreservationTests tlName ldl;
	let directory = getcwd () in 
		chdir "generated";
		Unix.open_process_in ("abella " ^ (tlName ^ ".thm") ^ " > " ^ (tlName ^ "_output.txt"));
		chdir directory;;
		
(*	try typecheck_tl tlRaw ; () with _ -> print_string tlName
*)	
		
let test = List.map testOne tlTable; print_string "All the specifications in input are type sound!\n";



	(*
	try output_string mycalculus_thm (generateThm tlName ldl) ; () with _ -> print_string tlName     
		
	let tlRaw2 = parseFile tlName in 
	if tlRaw = tlRaw2 then print_string tlName else print_string tlName
	let a = print_string tlName in 
*)	

