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
open Calculi

let sep = "\n\n"
let generateThm tsName ts = generateThmPreamble tsName ^ sep ^ (generateTheoremS (generateCanonicalFormsLemma ts)) ^ sep ^ (progressDefinition ts) ^ sep ^ (generateTheoremS (generateProgressLemmas ts)) ^ sep ^ (generateTheorem (generateProgressTheorem ts)) ^ sep ^ (generateTheorem (generatePreservationTheorem ts))

let tsTable = [
("stlc" , stlc) ; 
("stlc_parallel_red" , stlc_parallel_red) ; 
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
