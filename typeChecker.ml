
open Batteries
open Option
open List
open Aux
open TypedLanguage
open Ldl
open TypeCheckerProgress
open GenerateLambdaProlog
open LdlToTypedLanguage

(* ck (stands for "check") only serves for not being verbous in the following typechecker. defined in Aux *)

type roleDef = 
  	| Value of int list
  	| Error of int list

type roleTyp = 
	| ValueT of typeoperator * int list
  	| ErrorT of int list
	| Elim  of typeoperator
	| Derived 
	| ErrHandler 

type roleRed = 
	| Eliminates of termoperator 
	| EliminatesError 
	| Plain  


let rule_wellFormed2_ tl rule = 
	let op = ckIf (term_isConstructor (rule_getInputTerm rule)) (term_getConstructor (rule_getInputTerm rule)) ("rule not a valid typing rule: it does not type an operator") in 
	 rule_wellFormed2 (tl_lookupTermDecl tl op) rule
	 
let progressingArguments_are_contextual tl rule = 
	let op = rule_getConstructorOfInput rule in 
	let n = snd (positionsCheckedForValuehood rule) in 
	let ctx = term_getContextualPositions (tl_lookupTermDecl tl op) in 
		ckIf (list_subset n ctx) ctx ("Operator " ^ op ^ " has arguments tested for valuehood that are not contextual")

let typecheckVal tl rule = 
	if rule_wellFormed1 rule 
		then let op = (rule_getConstructorOfInput rule) in 
		 (op, Value (progressingArguments_are_contextual tl rule))
		else raise(Failure "typecheckVal") (* here rule_wellFormed1 has already raised its error *)
	
let typecheckErr tl rule = 
	if rule_wellFormed1 rule 
		then let op = (rule_getConstructorOfInput rule) in 
		 (op, Error (progressingArguments_are_contextual tl rule))
		else raise(Failure "typecheckErr") (* here rule_wellFormed1 has already raised its error *)

let tryErrorHandler op reductionsForOp =  
	match reductionsForOp with 
	| [rule1 ; rule2] -> ckIf (((not (rule_checkEliminatesSome rule1)) && (rule_checkEliminatesSome rule2)) || ((rule_checkEliminatesSome rule1) && (not (rule_checkEliminatesSome rule2))))
	     					 (op, ErrHandler)
		 					 ("Classification fails for " ^ op)
	| otherwise -> raise(Failure ("Classification fails for " ^ op))

let extractTypeOfEliminatingArgument rule = 
	        if (not (rule_typeCheckFirst rule)) 
				then raise(Failure "The typing rule of this eliminator does not assign a type to the eliminating argument")
				else 
					let assignedTypeEliminatingArg = (formula_getFirstOutput (rule_getFirstTypeCheck_prem rule)) in 
		      		ckIf (term_isConstructor assignedTypeEliminatingArg) (term_getConstructor assignedTypeEliminatingArg) ("Typing rule of this eliminator does not assign a constructed type to the eliminating argument")
					
						
let bindingDef_isValue bindingsDef op = if List.mem_assoc op bindingsDef 
										then match List.assoc op bindingsDef with 
										| Value n -> true 
										| Error n -> false
										else false 

let bindingTyp_sameTypeValue bindingsTyp op c1 = 
	if List.mem_assoc op bindingsTyp 
		then match List.assoc op bindingsTyp with 
		| ValueT(c2, n) -> c1 = c2
		| ErrorT n -> false
		else false 

let typecheckTyp tl reductionrules bindingsDef rule = 
	if rule_wellFormed2_ tl rule  
		then 
			let op = rule_getConstructorOfInput rule in 
			if List.mem_assoc op bindingsDef (* then it is a value or an error *)
			   then let assignedtype = (rule_getOutputTerm rule) in 
					match List.assoc op bindingsDef with 
					 | Value n -> let innerCheck = ckIf (term_isSkeletonFor (term_getConstructor assignedtype) assignedtype) (op, ValueT((term_getConstructor assignedtype), n)) ("The type assigned to the value " ^ op ^ "is not a constructed type") in 
									ckIf (term_isConstructor assignedtype) (innerCheck) ("The type assigned to the value " ^ op ^ "is not a constructed type")					
					| Error n -> ckIf (term_isFreeVar rule assignedtype) (op, ErrorT n) ("The type of the error is not a free variable")
			   else let reductionsForOp = List.filter (rule_isPredicateAndName reduction op) reductionrules in 
					 if (List.for_all  (fun rule -> not (rule_checkEliminatesSome rule)) reductionsForOp) 
					      then (op, Derived)   
						  else 
							  if (List.exists (fun rule -> not (rule_checkEliminatesSome rule)) reductionsForOp) 
								  then (tryErrorHandler op reductionsForOp) 
						  		  else ckIf (List.for_all (bindingDef_isValue bindingsDef) (List.map rule_checkEliminatesWhat reductionsForOp)) 
								  			(op, Elim (extractTypeOfEliminatingArgument rule)) 
								  			("Failed in Classifying operator " ^ op) 
		else raise(Failure "typecheckTyp") (* here rule_wellFormed2 has already raised its error *) 				
						 		
								
let typecheckRed tl bindingsTyp rule = 
	if rule_wellFormed1 rule 
		then 
			let op = (rule_getConstructorOfInput rule) in match List.assoc op bindingsTyp with
	(*
				| ValueT(c, n) -> raise(Failure "The value " ^ op ^ " has a reduction rule")
				| ErrorT n -> raise(Failure "The error " ^ op ^ "has a reduction rule")
		*)
				| Elim c -> 
					let op2 = rule_checkEliminatesWhat rule in 
					ckIf 
						( ck (bindingTyp_sameTypeValue bindingsTyp op2 c) ("The eliminator " ^ op ^ " for type " ^ c ^ " eliminates " ^ op2 ^ " which is not a value of that type") &&
				 		  ck (List.mem 1 (progressingArguments_are_contextual tl rule)) ("The eliminating argument of the eliminator " ^ op ^ " is not contextual"))
						(op, Eliminates op2) 
						("typecheckRed at Elim") (* here an error has already been raised *)
				| Derived -> 
					ckIf 
				 		  (ck (list_subset [] (progressingArguments_are_contextual tl rule)) ("Always true, this is just to run progressingArguments_are_contextual"))
						  (op, Plain) 
						  ("typecheckRed at Derived") (* here an error has already been raised *)
				| ErrHandler -> let n = progressingArguments_are_contextual tl rule in 
									if (rule_checkEliminatesSome rule) then (op, EliminatesError) else ckIf (List.mem 1 n) (op, Plain) ("The error handler does not have a reduction rule defined for values")
		else raise(Failure "typecheckRed") (* here rule_wellFormed1 has already raised its error *) 


let retrieveTypes bindingsTyp = 
	let valueToType bind = match bind with 
		| (op, ValueT(c, n)) -> Some c 	
		|_ -> None 
			in List.map get (List.filter is_some (List.map valueToType bindingsTyp))
			
let lookupValuesByTyp bindingsTyp typ = 
	let valueCollect bind = match bind with 
		| (op, ValueT(c, n)) -> if c = typ then Some op else None
		|_ -> None 
			in List.map get (List.filter is_some (List.map valueCollect bindingsTyp))

let lookupEliminatorsByTyp bindingsTyp typ = 
	let elimCollect bind = match bind with 
		| (op, Elim c) -> if c = typ then Some op else None
		|_ -> None 
			in List.map get (List.filter is_some (List.map elimCollect bindingsTyp))

let lookupEliminatorsByValue bindingsRed value = 
	let elimCollect bind = match bind with 
		| (op, Eliminates op2) -> if value = op2 then Some op else None
		|_ -> None 
			in List.map get (List.filter is_some (List.map elimCollect bindingsRed))

let presentErrorHandlerTyp bindingsTyp = List.mem ErrHandler (List.map snd bindingsTyp)
let consumedError bindingsRed = List.mem EliminatesError (List.map snd bindingsRed)

let uniqueness_of_bindingDef bindingsDef = 
	let operators = (List.map fst bindingsDef) in 
	let errorDeclarations = List.filter (fun role -> match role with Error n -> true | Value n -> false) (List.map snd bindingsDef) in 
	ckIf ((List.length operators = List.length (removeDuplicates operators)) && ((List.length errorDeclarations) < 2))
		 bindingsDef 
		 "Error, some operator has multiple value/error declarations." 	

let uniqueness_of_bindingTyp bindingsTyp = 
	let operators = (List.map fst bindingsTyp) in 
	ckIf (List.length operators = List.length (removeDuplicates operators)) bindingsTyp "Error, some operator has multiple typing rules or multiple roles in the language."

let check_exhaustiveness bindingsRed (typ, values, eliminators) = 
	let actualEliminators = combine values (List.map (lookupEliminatorsByValue bindingsRed) values) in 
	let checker (oneValue, itsEliminators) = 
(*		let check = ck (not (typ = "list")) ("values: " ^ String.concat "-" values ^ "\n eliminators: " ^ String.concat "-" itsEliminators) in *)
		ck (List.for_all (fun el -> List.mem el itsEliminators) eliminators) ("The value " ^ oneValue ^ "of type " ^ typ ^ " is not eliminated by all eliminators") in 
(*		   ck (difference = []) ("The value " ^ oneValue ^ "of type " ^ typ ^ "is not eliminated by the following eliminators: " ^ (String.concat "\n" difference)) in 
*)	 List.for_all checker actualEliminators 
	
let wellformed_final_bindings bindingsTyp bindingsRed = 
		 let types = retrieveTypes bindingsTyp in 
		   let valuesByType = combine types (List.map (lookupValuesByTyp bindingsTyp) types) in (* (type, values) *)
	 	 	let eliminatorsByTypes = List.map (lookupEliminatorsByTyp bindingsTyp) types in 
			 let valuesWithEliminators = List.map (fun ((typ, values), eliminators) -> (typ, values, eliminators)) (combine valuesByType eliminatorsByTypes) in (* (type, values, eliminiators *)
		  	  (List.for_all (check_exhaustiveness bindingsRed) valuesWithEliminators) &&
 			  if (presentErrorHandlerTyp bindingsTyp) then (ck (consumedError bindingsRed) ("The error handler do not eliminate the error")) else true 		  

let typecheck tlInput = 
	let errors = List.filter (rule_isPredicate errorPred) (tl_getRules tlInput) in 
	let values = List.filter (rule_isPredicate valuePred) (tl_getRules tlInput) in 
	let typing = List.filter rule_isTypingRule (tl_getRules tlInput) in 
	let reductionrules = List.filter (rule_isPredicate reduction) (tl_getRules tlInput) in 
	let bindingsDef = uniqueness_of_bindingDef (List.map (typecheckVal tlInput) values) @ (List.map (typecheckErr tlInput) errors) in 
	let bindingsTyp = uniqueness_of_bindingTyp (List.map (typecheckTyp tlInput reductionrules bindingsDef) typing) in 
	let bindingsRed = (List.map (typecheckRed tlInput bindingsTyp) reductionrules) in 
	  	(wellformed_final_bindings bindingsTyp bindingsRed) 
