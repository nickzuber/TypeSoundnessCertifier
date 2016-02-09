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
open SafeToTyped
open GenerateLambdaProlog
open PreservationTests
open Stlc
open Pairs
open Iff
open Lists
open ListsIsNil
open Fix
open Let
open Letrec
open Sums
open Unitt
open AbsImpl
open Exception
open Tuples
open Forall
open FullFledged

let checkResult output = 
    let extractNameOfRule = fun line -> let n = String.length "Abella < Query test_" in String.rchop (String.sub line n ((String.length line) - n)) in 
    let spotNoSolution = fun output -> fun i -> fun line -> 
		(let ok = "ok" in if String.exists line "No more" then if String.exists (List.at output (i-1)) "Query" then extractNameOfRule (List.at output (i-1)) else ok else ok) in
    let okLinesGoAway = fun line -> if line = "ok" then false else true in 
	let output2 = output in
	let errorsWithOkLines = List.mapi (spotNoSolution output2) output in 
	let failingRules = List.filter okLinesGoAway errorsWithOkLines in 
	if failingRules = [] then "Type Preservation: Succesfully checked! All the reductions rules preserve types.\n" else raise(Failure ("Type Preservation: Failed. The following reductions rules do not preserve types: " ^ (String.concat ", " failingRules) ^ "\n"))
	

let runPreservationTests (slName, sl) = 
	let test_thm = open_out ("./generated/test_" ^ slName ^ ".thm") in 
		output_string test_thm ("Specification \"" ^ slName ^ "\".\n\n");
		List.map (output_string test_thm) (List.map generateAbellaQuery (preservationTestsAsRules sl));
		close_out test_thm;
		let directory = getcwd () in 
			chdir "generated"; 
			let output = callAbella ("abella test_" ^ slName ^ ".thm") in 
				chdir directory;
				checkResult output;;
		  
let sep = "\n\n"
let generateThm tsName ts = generateThmPreamble tsName ^ sep ^ (generateTheoremS (generateCanonicalFormsLemma ts)) ^ sep ^ (progressDefinition ts) ^ sep ^ (generateTheoremS (generateProgressLemmas ts)) ^ sep ^ (generateTheorem (generateProgressTheorem ts))

let tsTable = [
(* CBN Calculi *)
("stlc_cbn" , stlc_cbn) ; 
("stlc_cbv" , stlc_cbv) ; 
("stlc_par" , stlc_par) ; 
("pairs_superlazy" , pairs_superlazy) ; 
("pairs_lazy" , pairs_lazy) ; 
("pairs_plain" , pairs_plain) ; 
("pairs_onlyfstButBoth" , pairs_onlyfstButBoth) ; 
("iff" , iff) ;
("lists", lists) ;
("lists_lazy", lists_lazy) ;
("listsIsNil", listsIsNil) ;
("listsIsNil_lazy", listsIsNil_lazy) ;
("sums", sums) ;
("unitt", unitt) ;
("absImpl_cbn", absImpl_cbn) ;
("absImpl_cbv", absImpl_cbv) ;
("absImpl_par", absImpl_par) ;
("tuples_lazy", tuples_lazy) ;
("tuples_parallel", tuples_parallel) ;
("tuples_plain", tuples_plain) ;
("foralll", forall) ;
(* STLC with if and booleans *)
("stlc_cbn_iff", stlc_cbn_iff) ;
("stlc_cbn_iff_par", stlc_cbn_iff_par) ;
("stlc_cbv_iff", stlc_cbv_iff) ;
("stlc_cbv_iff_par", stlc_cbv_iff_par) ;
("stlc_par_iff", stlc_par_iff) ;
("stlc_par_iff_par", stlc_par_iff_par) ;
(* STLC with pairs lazy, superlazy etcetera *)
("stlc_cbn_pairs_lazy", stlc_cbn_pairs_lazy) ;
("stlc_cbn_pairs_superlazy", stlc_cbn_pairs_superlazy) ;
("stlc_cbn_pairs_plain", stlc_cbn_pairs_plain) ;
("stlc_cbn_pairs_onlyfstButBoth", stlc_cbn_pairs_onlyfstButBoth) ;
("stlc_cbn_pairs_onlysnd", stlc_cbn_pairs_onlysnd) ;
("stlc_cbv_pairs_lazy", stlc_cbv_pairs_lazy) ;
("stlc_cbv_pairs_superlazy", stlc_cbv_pairs_superlazy) ;
("stlc_cbv_pairs_plain", stlc_cbv_pairs_plain) ;
("stlc_cbv_pairs_onlyfstButBoth", stlc_cbv_pairs_onlyfstButBoth) ;
("stlc_cbv_pairs_onlysnd", stlc_cbv_pairs_onlysnd) ;
("stlc_par_pairs_lazy", stlc_par_pairs_lazy) ;
("stlc_par_pairs_superlazy", stlc_par_pairs_superlazy) ;
("stlc_par_pairs_plain", stlc_par_pairs_plain) ;
("stlc_par_pairs_onlyfstButBoth", stlc_par_pairs_onlyfstButBoth) ;
("stlc_par_pairs_onlysnd", stlc_par_pairs_onlysnd) ;
(* STLC with lists *)
("stlc_cbn_lists", stlc_cbn_lists) ;
("stlc_cbn_lists_lazy", stlc_cbn_lists_lazy) ;
("stlc_cbv_lists", stlc_cbv_lists) ;
("stlc_cbv_lists_lazy", stlc_cbv_lists_lazy) ;
("stlc_par_lists", stlc_par_lists) ;
("stlc_par_lists_lazy", stlc_par_lists_lazy) ;
(* STLC with lists with booleans and isNil *)
("stlc_cbn_listsIsNil", stlc_cbn_listsIsNil) ;
("stlc_cbn_listsIsNil_lazy", stlc_cbn_listsIsNil_lazy) ;
("stlc_cbv_listsIsNil", stlc_cbv_listsIsNil) ;
("stlc_cbv_listsIsNil_lazy", stlc_cbv_listsIsNil_lazy) ;
("stlc_par_listsIsNil", stlc_par_listsIsNil) ;
("stlc_par_listsIsNil_lazy", stlc_par_listsIsNil_lazy) ;
(* STLC with fix *)
("stlc_cbn_fix", stlc_cbn_fix) ;
("stlc_cbv_fix", stlc_cbv_fix) ;
("stlc_par_fix", stlc_par_fix) ;
(* STLC with let *)
("stlc_cbn_let", stlc_cbn_let) ;
("stlc_cbv_let", stlc_cbv_let) ;
("stlc_par_let", stlc_par_let) ;
(* STLC with letrec *)
("stlc_cbn_letrec", stlc_cbn_letrec) ;
("stlc_cbv_letrec", stlc_cbv_letrec) ;
("stlc_par_letrec", stlc_par_letrec) ;
(* STLC with sums *)
("stlc_cbn_sums", stlc_cbn_sums) ;
("stlc_cbv_sums", stlc_cbv_sums) ;
("stlc_par_sums", stlc_par_sums) ;
(* STLC with unit *)
("stlc_cbn_unitt", stlc_cbn_unitt) ;
("stlc_cbv_unitt", stlc_cbv_unitt) ;
("stlc_par_unitt", stlc_par_unitt) ;
(* STLC with exceptions *)
("stlc_cbn_exc", stlc_cbn_exc) ;
("stlc_cbv_exc", stlc_cbv_exc) ;
("stlc_par_exc", stlc_par_exc) ;
(* STLC with tuples lazy, parallel and plain *)
("stlc_cbn_tuples_lazy", stlc_cbn_tuples_lazy) ;
("stlc_cbn_tuples_parallel", stlc_cbn_tuples_parallel) ;
("stlc_cbn_tuples_plain", stlc_cbn_tuples_plain) ;
("stlc_cbv_tuples_lazy", stlc_cbv_tuples_lazy) ;
("stlc_cbv_tuples_parallel", stlc_cbv_tuples_parallel) ;
("stlc_cbv_tuples_plain", stlc_cbv_tuples_plain) ;
("stlc_par_tuples_lazy", stlc_par_tuples_lazy) ;
("stlc_par_tuples_parallel", stlc_par_tuples_parallel) ;
("stlc_par_tuples_plain", stlc_par_tuples_plain) ;
(* System F *)
("stlc_cbn_forall", stlc_cbn_forall) ;
("stlc_cbv_forall", stlc_cbv_forall) ;
("stlc_par_forall", stlc_par_forall) ;
(* FullFledged Language: System F with if-then-else and booleans, lists, exceptions and letrec *)
("fullFledged_cbn", fullFledged_cbn) ;
("fullFledged_cbv", fullFledged_cbv) ;
("fullFledged_par", fullFledged_par) ;
]

let lookup_typesystem tsName = List.assoc tsName tsTable  

let g slName =
	let sl = lookup_typesystem slName in 
	let tl = compile sl in 
	let mycalculus_sig = open_out ("./generated/" ^ slName ^ ".sig") in
	let mycalculus_mod = open_out ("./generated/" ^ slName ^ ".mod") in
	let mycalculus_thm = open_out ("./generated/" ^ slName ^ ".thm") in
 	output_string mycalculus_sig (generateSignature slName tl);
    output_string mycalculus_mod (generateModule slName tl);
	output_string mycalculus_thm (generateThm slName sl); 
    close_out mycalculus_sig;
    close_out mycalculus_mod;
    close_out mycalculus_thm;
	runPreservationTests (slName, sl);
	let directory = getcwd () in 
		chdir "generated";
		Unix.open_process_in ("abella " ^ (slName ^ ".thm") ^ " > " ^ (slName ^ "_output.txt"));
		chdir directory;;

let compileAll () = (List.map compile (List.map snd tsTable))
let typecheckAll () = List.map typecheck_tl (List.map compile (List.map snd tsTable))
let test () = List.map g (List.map fst tsTable) 
let typecheckAndTest () = typecheckAll (); test ();;
let test_preservation () = List.map runPreservationTests tsTable
let typecheck sl = typecheck_tl (compile sl)


(* 
TO DO: 
- type preservation
- tuples and ListException
- better story for exhaustiveness in progress.
- write the paper

typechecker_sl stlc_cbn ;;
let typecheckerWrapper (tl, name) = try typechecker tl with Failure e -> raise(Failure("Failure in the system: " ^ name))
let test_typecheckW () = List.map typecheckerWrapper (List.zip (List.map compile (List.map snd tsTable)) (List.map fst tsTable))
*)

