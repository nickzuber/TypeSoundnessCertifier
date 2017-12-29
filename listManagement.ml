
open Batteries
open Aux
open Option
open TypedLanguage
open Ldl

let emptyList c = "empty_" ^ c
let emptyListT c = "emptyT_" ^ (chop_last_char c 'T')
let consList c = "cons_" ^ c
let consListT c = "consT_" ^ (chop_last_char c 'T')
let termList c = "list_" ^ c
let typeList c = "list_T" ^ c
let termListMember c = c ^ "_member" 
let typeListMember c = c ^ "T_member" 
let termListUpdate c = c ^ "_update"
let toRecordName c = c ^ "T"
let typeOfWithSelf = "typeOfWithSelf" 

let memberCasesLemma c = c ^ "_member_cases"
let memberSynchLemma c = c ^ "_member_synch"
let memberSynchLemmaForSelf c = c ^ "_member_synch_TypeOfWithSelf" 
let memberPreservationLemma = "member_preserve"
let memberPreserveLemmaForSelf = "member_preserve_TypeOfWithSelf" 
let updateSynchLemma c = c ^ "_update_synch"
let updatePreservationLemma = "update_preserve"

let unique_lemma memberPred = memberPred ^ "_unique"

let list_width c = c ^ "_width"

let term_getEmptyList c = Constructor("empty_" ^ c, [])
 
let typeEntry_isList te = match te with 
	| List(_) -> true 
	| ListSelf(_) -> true 
	| _ -> false 

let typeEntry_isSelfList te = match te with 
	| ListSelf(_) -> true 
	| _ -> false 

let termDecl_isList termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> if arguments == [] then false else typeEntry_isList (List.hd arguments)
let typeDecl_isList typeDecl = match typeDecl with DeclType(c, arguments) -> if arguments == [] then false else typeEntry_isList (List.hd arguments)
let termDecl_isSelfList termDecl = match termDecl with DeclTrm(c, valpos, ctx, arguments) -> if arguments == [] then false else typeEntry_isSelfList (List.hd arguments)
let typeDecl_isSelfList typeDecl = match typeDecl with DeclType(c, arguments) -> if arguments == [] then false else typeEntry_isSelfList (List.hd arguments)
let termDecl_isListButNotSelf termDecl = termDecl_isList termDecl && (not (termDecl_isSelfList termDecl))
let typeDecl_isListButNotSelf typeDecl = typeDecl_isList typeDecl && (not (typeDecl_isSelfList typeDecl))
	
let termEntry_list_getElements te = match te with | List(_,_,trm) -> trm | ListSelf(_,_,trm) -> trm 
let termDecl_list_getElements termDecl = termEntry_list_getElements (List.hd (termDecl_getArguments termDecl))
let typeDecl_list_getElements typeDecl = termEntry_list_getElements (List.hd (type_getArguments typeDecl))


let tl_getLists tl = List.filter termDecl_isList (tl_getTerms tl) 
let ldl_getLists_typeDecls ldl = List.filter typeDecl_isList (List.map specType_getSig (ldl_getTypes ldl))
let ldl_getLists_names ldl = List.map type_getOperator (ldl_getLists_typeDecls ldl)

let ldl_contains_lists ldl c =  
	let typeDecl = try Some (specType_getSig (ldl_lookup_typeSpec ldl c)) with _ -> None in 
	if is_none typeDecl then false else typeDecl_isList (get typeDecl)

let lists_addTypes termDecl = 
	if termDecl_isList termDecl 
		then let c = term_getOperator termDecl in 
				[DeclType(c ^ "T", [Simple(Inv, typeList c)])]
		else []

let list_isInvariant typeDecl = type_getListVariance typeDecl = Inv

(* typeOf (record List1) (recordT List2) :- typeOfWithSelf (recordT List2) (record List1) (recordT List2). *)
let rule_typeOfTheSelfList c = Rule("", [Formula(typeOfWithSelf, [Constructor(c ^ "T", [Var "List2"]) ; Constructor(c, [Var "List1"])], [Constructor(c ^ "T", [Var "List2"])])], 
										Formula(typing, [Constructor(c, [Var "List1"])], [Constructor(c ^ "T", [Var "List2"])])
									)
let rule_typeOfEmptyList selfFlag c = 
	if selfFlag 
		(* typeOfWithSelf (recordT Whole) (record (empty_record )) (recordT (emptyT_record )). *)
		then Rule("", [], Formula(typeOfWithSelf, [Constructor(c ^ "T", [Var "Whole"]) ; Constructor(c, [Constructor(emptyList c, [])])], [Constructor(c ^ "T", [Constructor(emptyListT c, [])])]))
		else Rule("", [], Formula(typing, [Constructor(c, [Constructor(emptyList c, [])])], [Constructor(c ^ "T", [Constructor(emptyListT c, [])])]))
let rule_typeOfConsList termDecl = 
	let c = term_getOperator termDecl in 
	let elementsType = termDecl_list_getElements termDecl in 
	let consInput = Constructor(consList c, [Var "L" ; Var "E" ; Var "Rest1"]) in 
	let consOutput = Constructor(consListT c, [Var "L" ; elementsType ; Var "Rest2"]) in 
	let whole = Constructor(c ^ "T", [Var "Whole"]) in 
	 if termDecl_isSelfList termDecl 
		then
			(* typeOfWithSelf (recordT Whole) (record (cons_record L E Rest1)) (recordT (consT_record L (arrow T1 T2) Rest2)) :- (pi x\ typeOf x (recordT Whole) => typeOf (E x) (arrow T1 T2)), typeOfWithSelf (recordT Whole) (record Rest1) (recordT Rest2). *) 
			Rule("t_" ^ c ^ "cons", [  
						Hypothetical(Formula(typing, [Var "x"], [whole]), Formula(typing, [Application(Var "E", Var "x")], [elementsType]))  ;
				   		Formula(typeOfWithSelf, [whole ; Constructor(c, [Var "Rest1"])], [Constructor(c ^ "T", [Var "Rest2"])]) ;  
					 ],
			            Formula(typeOfWithSelf, [whole ; Constructor(c, [consInput])], [Constructor(c ^ "T", [consOutput])])
				   ) 
		else  Rule("t_" ^ c ^ "cons", [  
						Formula(typing, [Var "E"], [elementsType]) ;
				   		Formula(typing, [Constructor(c, [Var "Rest1"])], [Constructor(c ^ "T", [Var "Rest2"])]) 
					 ],
			            Formula(typing, [Constructor(c, [consInput])], [Constructor(c ^ "T", [consOutput])])
				   )
let tl_generateLanguageWithLists termDecls = TypedLanguage(List.concat (List.map lists_addTypes termDecls),[],[])

let fakeRule = Rule("", [], Formula("", [],[]))
let list_replace_cons_with_list rule c = match rule with Rule(name, premises, Formula(pred, [lesser ; greater], [])) -> 
	 Rule("t_" ^ c ^ "emptyList" , premises, Formula(pred, [lesser ; Constructor(c, [Var "List"])], []))

let listOperations tl = 
	let success predicate consName variable = Rule(consName ^ "_member1" , [], Formula(predicate, [Constructor(consName, [Var "L" ; Var variable ; Var "Rest"]) ; Var "L" ; Var variable], [])) in 
	let recursiveSearch predicate consName variable = Rule(consName ^ "_member2" , [Formula(predicate, [Var "Rest" ; Var "L" ; Var variable], [])], Formula(predicate, [Constructor(consName, [Var "L1" ; Var (variable ^ "1")  ; Var "Rest"]) ; Var "L" ; Var variable], [])) in 
	let rulesForMember termDecl =  
		let c = term_getOperator termDecl in 
		[
		 success (termListMember c) (consList c) "T"; 
		 recursiveSearch (termListMember c) (consList c) "T"; 
		 success (typeListMember c) (consListT c)  "E" ; 
		 recursiveSearch (typeListMember c) (consListT c) "E"  
		] in 
	let rulesForUpdate termDecl =  
		let c = term_getOperator termDecl in 
		let consName = (consList c) in 
		[
		(* success case *)
		 Rule(c ^ "_update1" , [], Formula((termListUpdate c), 
		 									[Constructor(consName, [Var "L" ; Var "E1" ; Var "Rest"]) ; Var "L" ; Var "E2" ; Constructor(consName, [Var "L" ; Var "E2" ; Var "Rest"])], []))
		; 
 		(* recursive case *)
		 Rule(c ^ "_update2" , 
		 		[Formula((termListUpdate c), [Var "Rest" ; Var "L2" ; Var "E2" ; Var "Rest2"], [])], 
		 		Formula((termListUpdate c), [Constructor(consName, [Var "L1" ; Var "E1" ; Var "Rest"]) ; Var "L2" ; Var "E2" ; Constructor(consName, [Var "L1" ; Var "E1" ; Var "Rest2"])], []))
		]
		in List.concat (List.map rulesForMember (tl_getLists tl)) @ List.concat (List.map rulesForUpdate (tl_getLists tl))


let adjustContextsIfList termDecl ctxPositions = 
	if termDecl_isList termDecl 
			then match ctxPositions with
				| [3] -> [] 
				| _ -> [1 ; 2] 
			else ctxPositions
			
let rule_doesItUseUpdate_ rules c = 
	match rules with 
			| [(Rule(_, (premise :: rest), _))] -> formula_isPredicate (termListUpdate c) premise 
			| _ -> false 
			
let rule_doesItUseUpdate termSpec typeSpec = 
	let rules = (specTerm_getReduction termSpec) in 
	let argumentsToTerm = termDecl_getArguments (specTerm_getSig termSpec) in 
	let typeOperator = (specType_getTypeName typeSpec) in 
	let c = (chop_last_char typeOperator 'T') in 
	if rule_doesItUseUpdate_ rules c
		then (
			let premise = List.hd (rule_getPremises (List.hd rules)) in 
			  match (formula_getInputs premise @ formula_getOutputs premise) with 
						(*term_getFormalVarByType adds a +1 to indexes, so here we do a -1 *)
						(*Here the assumption is that the var that we look for is always the last argument *)
						| [_ ; _ ; var ; _] -> Some (term_getFormalVarByType argumentsToTerm ((List.length argumentsToTerm) -1) (List.last argumentsToTerm))
						| _ -> raise(Failure("rule_doesItUseUpdate: a formula uses update but not with the correct arguments: " ^ (dump (List.hd rules) ^ "--" ^ (dump (formula_getInputs premise)))))
			)
		else None
	
let ldl_getListsThatUseUpdate_typeDecls ldl = 
	let typeSpec_UseUpdate specType = let c = (chop_last_char (specType_getTypeName specType) 'T') in 
		List.exists (fun x -> rule_doesItUseUpdate_ x c) (List.map (fun x -> [x]) (List.concat (List.map specTerm_getReduction (specType_getEliminators specType)))) in
	 		List.map specType_getSig (List.filter typeSpec_UseUpdate (ldl_getTypes ldl))

