open Batteries
open Enum
open Unix
open Aux
open Type_system
open Proof
open Values
open Errors
open ContextualRules
open ErrorContexts
open CanonicalForms
open Progress
open PreservationTests
open Preservation
open GenerateLambdaProlog
open CalculiCBN
open CalculiPAR
open CalculiCBV

let sep = "\n\n"
let generateThm tsName ts = generateThmPreamble tsName ^ sep ^ (generateTheoremS (generateCanonicalFormsLemma ts)) ^ sep ^ (progressDefinition ts) ^ sep ^ (generateTheoremS (generateProgressLemmas ts)) ^ sep ^ (generateTheorem (generateProgressTheorem ts)) ^ sep ^ (generateTheorem (generatePreservationTheorem ts))

let tsTable = [
(* CBN Calculi  *)
("stlc" , stlc) ; 
("stlc_exc" , stlc_exc) ; 
("stlc_fix" , stlc_fix) ; 
("stlc_if" , stlc_if) ; 
("stlc_inf" , stlc_inf) ;
("stlc_let" , stlc_let) ;
("stlc_letrec" , stlc_letrec) ;
("stlc_lists" , stlc_lists) ;
("stlc_pairs" , stlc_pairs) ;
("stlc_sum" , stlc_sum) ;
("stlc_tuples" , stlc_tuples) ;
("stlc_unit" , stlc_unit) ;
("systemF" , systemF) ;
("fullFledged" , fullFledged) ;
(* Par Calculi (parallel reduction) *)
("stlc_par" , stlc_par) ; 
("stlc_par_exc" , stlc_par_exc) ; 
("stlc_par_fix" , stlc_par_fix) ; 
("stlc_par_if" , stlc_par_if) ; 
("stlc_par_inf" , stlc_par_inf) ;
("stlc_par_let" , stlc_par_let) ;
("stlc_par_letrec" , stlc_par_letrec) ;
("stlc_par_lists" , stlc_par_lists) ;
("stlc_par_pairs" , stlc_par_pairs) ;
("stlc_par_sum" , stlc_par_sum) ;
("stlc_par_tuples" , stlc_par_tuples) ;
("stlc_par_unit" , stlc_par_unit) ;
("systemF_par" , systemF_par) ;
("fullFledged_par" , fullFledged_par) ;
(* CBV Calculi (not supported yet) *)
]

let lookup_typesystem tsName = List.assoc tsName tsTable  

let g tsName =
	let tsOriginal = lookup_typesystem tsName in 
	let tsWithValues = (generateValues tsOriginal) in 
	let tsWithErrors = (generateErrors tsWithValues) in 
	let tsWithContexts = (generateContextualRules tsWithErrors) in 
	let ts = (generateErrorContexts tsWithContexts) in 
	let mycalculus_sig = open_out ("./generated/" ^ tsName ^ ".sig") in
	let mycalculus_mod = open_out ("./generated/" ^ tsName ^ ".mod") in
	let mycalculus_thm = open_out ("./generated/" ^ tsName ^ ".thm") in
 	output_string mycalculus_sig (generateSignature tsName ts);
    output_string mycalculus_mod (generateModule tsName ts);
	output_string mycalculus_thm (generateThm tsName ts); 
    close_out mycalculus_sig;
    close_out mycalculus_mod;
    close_out mycalculus_thm;
	let porcatroia = getcwd () in 
		chdir "generated";
		Unix.open_process_in ("abella " ^ (tsName ^ ".thm") ^ " > " ^ (tsName ^ "_output.txt"));
		chdir porcatroia;;

		(* 	
			let filelines = File.lines_of ("./" ^ tsName ^ "_output.txt") in
	(drop ((count filelines) - 1) filelines);
	match get filelines with Some x -> if String.exists x "Goodbye" then print_string (tsName ^ ": PASSED.\n") else print_string (tsName ^ ": FAILED.\n");
 *)

let test () = List.map g (List.map fst tsTable) 

let runPreservationTests dummy = let () = chdir "generated" in let output = callAbella "abella ./mycalculusTests.thm" in let () = chdir "../" in
         let extractNameOfRule = fun line -> let n = String.length "Abella < Query test_" in String.rchop (String.sub line n ((String.length line) - n)) in 
         let spotNoSolution = fun output -> fun i -> fun line -> let ok = "ok" in  
          if String.exists line "No more" then if String.exists (List.at output (i-1)) "Query" then extractNameOfRule (List.at output (i-1)) else ok else ok in
         let okLinesGoAway = fun line -> if line = "ok" then false else true in 
         let output2 = output in
         let errorsWithOkLines = List.mapi (spotNoSolution output2) output in 
         let failingRules = List.filter okLinesGoAway errorsWithOkLines in 
          if failingRules = [] then "Type Preservation: Succesfully checked! All the reductions rules preserve types.\n" else "Type Preservation: Failed. The following reductions rules do not preserve types: " ^ String.concat ", " failingRules ^ "\n"
