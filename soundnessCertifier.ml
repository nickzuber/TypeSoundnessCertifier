open Batteries
open Option
open Enum
open List
open Unix
open Aux
open TypedLanguage
open Ldl
open ListLemmas
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
open LdlToTypedLanguage
open GenerateLambdaProlog
open TypeCheckerPreservation 
open Parser
open Subtyping

let sep = "\n\n"
let generateThm tsName ldl subtyping = generateThmPreamble tsName 
							^ sep ^ 
							(generateTheoremS (generateSubtypingLemmas ldl subtyping)) 
							^ sep ^ 
							(generateTheoremS (generateCanonicalFormsLemma ldl subtyping)) 
							^ sep ^ 
							(progressDefinition ldl) 
							^ sep ^ 
							(generateTheoremS (generateProgressLemmas ldl subtyping)) 
							^ sep ^ 
							(generateTheorem (generateProgressTheorem ldl subtyping)) 
							^ sep ^
 							(generateTheoremS (generatePreservationTheorem ldl subtyping)) 
							^ sep ^ 
							typesoundnessProof 
							
let checkResult tlName output = 
	if (String.exists (last output) "< search.") 
		(* if Abella 2.0.2, 2.0.3, and 2.0.4 fail our type preservation check, they quit abruptly after "search.", which is then the last line *)
		(* this check above will be replaced with a better way to interact with Abella *)
		then raise(Failure("FAILED Type Preservation. Specification: " ^ tlName ^ ". Rule: " ^ String.tail (fst (String.split (last output) "<")) (String.length "test_") ^ "\n"))
		else ()

let runPreservationTests tlName ldl subtyping = 
	(* timeout is 3 seconds, with gtimeout 
	let timeout = "" in 
	let timeout = " gtimeout 3s " in 
	*)
	let timeout = "" in 
	let test_thm = open_out ("./generated/test_" ^ tlName ^ ".thm") in 
		output_string test_thm ("Specification \"" ^ tlName ^ "\".\n\n");
		List.map (output_string test_thm) (List.map generateAbellaQuery (preservationTestsAsRules ldl subtyping)); 
		close_out test_thm;
		let directory = getcwd () in 
			chdir "generated"; 
			let output = callAbella (timeout ^ "abella test_" ^ tlName ^ ".thm") in 
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
"pairs_leftToRight" ; 
"pairs_onlyfstButBoth" ; 
"iff" ;
"lists" ;
"lists_lazy" ;
"lists_lefToright" ;
"listsIsNil";
"listsIsNil_lazy" ;
"listsIsNil_lefToright" ;
"sums" ;
"unitt" ;
"itlc_cbn" ;
"itlc_cbv" ;
"itlc_par" ;
"tuples_plain" ;
"tuples_lazy" ;
"tuples_parallel" ;
"tuples_lefToright" ;
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
"stlc_cbn_pairs_lefToright" ;
"stlc_cbn_pairs_onlyfstButBoth" ;
"stlc_cbn_pairs_onlysnd" ;
"stlc_cbv_pairs_lazy" ;
"stlc_cbv_pairs_superlazy" ;
"stlc_cbv_pairs_plain" ;
"stlc_cbv_pairs_lefToright" ;
"stlc_cbv_pairs_onlyfstButBoth" ;
"stlc_cbv_pairs_onlysnd" ;
"stlc_par_pairs_lazy" ;
"stlc_par_pairs_superlazy" ;
"stlc_par_pairs_plain" ;
"stlc_par_pairs_lefToright" ;
"stlc_par_pairs_onlyfstButBoth" ;
"stlc_par_pairs_onlysnd" ;
(* STLC with lists *)
"stlc_cbn_lists" ;
"stlc_cbn_lists_lazy" ;
"stlc_cbn_lists_lefToright" ;
"stlc_cbv_lists" ;
"stlc_cbv_lists_lazy" ;
"stlc_cbv_lists_lefToright" ;
"stlc_par_lists" ;
"stlc_par_lists_lazy" ;
"stlc_par_lists_lefToright" ;
(* STLC with lists with booleans and isNil *)
"stlc_cbn_listsIsNil" ;
"stlc_cbn_listsIsNil_lazy" ;
"stlc_cbn_listsIsNil_lefToright" ;
"stlc_cbv_listsIsNil" ;
"stlc_cbv_listsIsNil_lazy" ;
"stlc_cbv_listsIsNil_lefToright" ;
"stlc_par_listsIsNil" ;
"stlc_par_listsIsNil_lazy" ;
"stlc_par_listsIsNil_lefToright" ;
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
"stlc_cbn_tuples_lefToright" ;
"stlc_cbv_tuples_lazy" ;
"stlc_cbv_tuples_parallel" ;
"stlc_cbv_tuples_plain" ;
"stlc_cbv_tuples_lefToright" ;
"stlc_par_tuples_lazy" ;
"stlc_par_tuples_parallel" ;
"stlc_par_tuples_plain" ;
"stlc_par_tuples_lefToright" ;
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
"lists_withMore_leftToRight_cbv" ;
"lists_withMore_leftToRight_cbn" ;
"lists_withMore_leftToRight_par" ;
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
"fpl_cbv" ;
(* Subtyping 
   fpl_cbv_sub: is Fpl but without recursive types. *)
"fpl_cbv_sub" ;
"systemFsub" ;
"systemFsub_kernel" ;
"systemFsub_records" ;
"systemFsub_records_invariant" ;
"systemFsub_records_invariant_2" ;    
"systemFsub_records_noWidth" ;
"systemFsub_records_invoke" ;
]

let testOne tlName =
	let (tlRaw, subtypingRaw) = parseFile tlName in 
	(try typecheck tlRaw with | Failure errorMessage -> raise(Failure("Typechecker Failure for " ^ tlName ^ ": " ^ errorMessage)));
	let ldl = (try typecheck_tl tlRaw subtypingRaw with | Failure errorMessage -> raise(Failure("Failure for " ^ tlName ^ ": " ^ errorMessage))) in 
	let tl = compile ldl in 	
	let subtyping = subtyping_expand ldl subtypingRaw in 
	let mycalculus_sig = open_out ("./generated/" ^ tlName ^ ".sig") in
	let mycalculus_mod = open_out ("./generated/" ^ tlName ^ ".mod") in
	let mycalculus_thm = open_out ("./generated/" ^ tlName ^ ".thm") in
 	output_string mycalculus_sig (generateSignature tlName tl);
	output_string mycalculus_sig (subtyping_declaration subtyping);
	output_string mycalculus_mod (generateModule tlName tl);	
	output_string mycalculus_mod (generateRules (subtyping_definition ldl subtyping));
	output_string mycalculus_thm (generateThm tlName ldl subtyping); 
    close_out mycalculus_sig;
    close_out mycalculus_mod;
    close_out mycalculus_thm;
	runPreservationTests tlName ldl subtyping; 
	let directory = getcwd () in 
		chdir "generated";
		Unix.open_process_in ("abella " ^ (tlName ^ ".thm") ^ " > " ^ (tlName ^ "_output.txt"));
		chdir directory;;

	
		
let test = List.map testOne tlTable; print_string "All the specifications in input are type sound!\n";


