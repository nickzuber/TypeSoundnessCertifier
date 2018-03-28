(*
  While Language - a Hackerrank FP challenge:
  https://www.hackerrank.com/challenges/while-language-fp

  Stmts ::= Stmt | Stmt ';' Stmts
  Stmt ::= Assign | IfElse | While
  Assign ::= Identifier ':=' AExp
  IfElse ::= 'if' BExp 'then' '{' Stmts '}' 'else' '{' Stmts '}'
  While ::= 'while' BExp 'do' '{' Stmts '}'

  Exp ::= OrExp
  OrExp ::= AndExp ( 'or' AndExp )*
  AndExp ::= ROpExp (' and' ROpExp )*
  ROpExp ::= PlusSubExp [ ('>' | '<') PlusSubExp ]
  PlusSubExp ::= MulDivExp ( ['+' | '-'] MulDivExp )*
  MulDivExp ::= PrimaryExp ( ['*' | '/'] PrimaryExp )*
  PrimaryExp ::= '(' Exp ')' | Identifier | Number | Bool

  Bool ::= 'true' | 'false'
  Number ::= ([0-9])+
  Identifier ::= [A-Za-z][a-zA-Z0-9]*
*)

(* ----------------------------- opal.ml START ------------------------------ *)

module LazyStream = struct
  type 'a t = Cons of 'a * 'a t Lazy.t | Nil
  let of_stream stream =
    let rec next stream =
      try Cons(Stream.next stream, lazy (next stream))
      with Stream.Failure -> Nil
    in
    next stream
  let of_string str = str |> Stream.of_string |> of_stream
  let of_channel ic = ic |> Stream.of_channel |> of_stream
  let of_function f =
    let rec next f =
      match f () with
      | Some x -> Cons(x, lazy (next f))
      | None -> Nil
    in
    next f
end

let implode l = String.concat "" (List.map (String.make 1) l)
let explode s =
  let l = ref [] in
  String.iter (fun c -> l := c :: !l) s;
  List.rev !l
let (%) f g = fun x -> g (f x)
type 'token input = 'token LazyStream.t
type ('token, 'result) parser = 'token input -> ('result * 'token input) option
let parse parser input =
  match parser input with
  | Some(res, _) -> Some res
  | None -> None
let return x input = Some(x, input)
let (>>=) x f =
  fun input ->
    match x input with
    | Some(result', input') -> f result' input'
    | None -> None
let (<|>) x y =
  fun input ->
    match x input with
    | Some _ as ret -> ret
    | None -> y input
let rec scan x input =
  match x input with
  | Some(result', input') -> LazyStream.Cons(result', lazy (scan x input'))
  | None -> LazyStream.Nil
let mzero _ = None
let any = function
  | LazyStream.Cons(token, input') -> Some(token, Lazy.force input')
  | LazyStream.Nil -> None
let satisfy test = any >>= (fun res -> if test res then return res else mzero)
let eof x = function LazyStream.Nil -> Some(x, LazyStream.Nil) | _ -> None
let (=>) x f = x >>= fun r -> return (f r)
let (>>) x y = x >>= fun _ -> y
let (<<) x y = x >>= fun r -> y >>= fun _ -> return r
let (<~>) x xs = x >>= fun r -> xs >>= fun rs -> return (r :: rs)
let rec choice = function [] -> mzero | h :: t -> (h <|> choice t)
let rec count n x = if n > 0 then x <~> count (n - 1) x else return []
let between op ed x = op >> x << ed
let option default x = x <|> return default
let optional x = option () (x >> return ())
let rec skip_many x = option () (x >>= fun _ -> skip_many x)
let skip_many1 x = x >> skip_many x
let rec many x = option [] (x >>= fun r -> many x >>= fun rs -> return (r :: rs))
let many1 x = x <~> many x
let sep_by1 x sep = x <~> many (sep >> x)
let sep_by x sep = sep_by1 x sep <|> return []
let end_by1 x sep = sep_by1 x sep << sep
let end_by x sep = end_by1 x sep <|> return []
let chainl1 x op =
  let rec loop a = (op >>= fun f -> x >>= fun b -> loop (f a b)) <|> return a in
  x >>= loop
let chainl x op default = chainl1 x op <|> return default
let rec chainr1 x op =
  x >>= fun a -> (op >>= fun f -> chainr1 x op >>= f a) <|> return a
let chainr x op default = chainr1 x op <|> return default
let exactly x = satisfy ((=) x)
let one_of  l = satisfy (fun x -> List.mem x l)
let none_of l = satisfy (fun x -> not (List.mem l x))
let range l r = satisfy (fun x -> l <= x && x <= r)
let space     = one_of [' '; '\t'; '\r'; '\n']
let spaces    = skip_many space
let newline   = exactly '\n'
let tab       = exactly '\t'
let upper     = range 'A' 'Z'
let lower     = range 'a' 'z'
let digit     = range '0' '9'
let letter    = lower  <|> upper
let alpha_num = letter <|> digit <|> exactly '\'' <|> exactly '_'
let hex_digit = range 'a' 'f' <|> range 'A' 'F'
let oct_digit = range '0' '7'
let lexeme x = spaces >> x
let token s =
  let rec loop s i =
    if i >= String.length s
    then return s
    else exactly s.[i] >> loop s (i + 1)
  in
  lexeme (loop s 0)
(* ------------------------------ opal.ml END ------------------------------- *)

open Aux
open TypedLanguage
open ListManagement
open Subtyping
open GenerateLambdaProlog

type exp = PlusExp of exp * exp
         | SubExp of exp * exp
         | MulExp of exp * exp
         | DivExp of exp * exp
         | Variable of string
         | Number of int
         | LTExp of exp * exp
         | GTExp of exp * exp
         | AndExp of exp * exp
         | OrExp of exp * exp
         | Bool of bool

type prog = Stmts of prog list
          | Assign of string * exp
          | IfElse of exp * prog * prog
          | While of exp * prog

exception Syntax_error
exception Runtime_error

(* parser *)

let last l = List.nth l ( (List.length l) - 1 )
let remove_last lst = List.rev (List.tl (List.rev lst))

let ctxTag = "% context"
let subsumptionTag = "% declarative-subtyping"
let subtyping_top_Tag = "% subtyping-top"
let subtyping_special_Tag = "% subtyping-for"
let contravariantTag = "% contravariant"
let invariantTag = "% invariant"
let recursiveTag = "% recursive"
let listInfoTag = "% list-info"
let listKeyword = "record-list"
let listSelfKeyword = "list-with-self"
let widthKeyword = "width"
let reserved = ["(x)E" ; "(X)E" ; "(X)T" ; "value" ; "error" ; "Gamma |- " ; "Gamma |- x : " ;  "Gamma |- X," ; "Gamma, X <: " ; "-->" ; "<==" ; "." ; "/\\" ; "(" ; ")" ; "[" ; "/x]" ; "/X]" ; "<:" ; "Gamma, X +++ "  ;
				"Expression E ::= x | " ; "Expression E ::= " ; "Type T ::= X | " ; "Type T ::= " ; "Value V ::= " ; "Context C ::= [] | " ; "Gamma ::= 0 | " ; "|" ;
				
				]

let ident = (spaces >> letter <~> many alpha_num) => implode >>= function
  | s when List.mem s reserved -> mzero
  | s -> return s

let var = (spaces >> upper <~> many alpha_num) => implode >>= function s -> return s

let number = spaces >> many1 digit => implode % int_of_string

let parens = between (token "(") (token ")")
let addop = token "+" >> return (fun x y -> PlusExp(x, y))
let subop = token "-" >> return (fun x y -> SubExp(x, y))
let mulop = token "*" >> return (fun x y -> MulExp(x, y))
let divop = token "/" >> return (fun x y -> DivExp(x, y))
let ltop  = token "<" >> return (fun x y -> LTExp(x, y))
let gtop  = token ">" >> return (fun x y -> GTExp(x, y))
let orop  = token "or"  >> return (fun x y -> OrExp(x, y))
let andop = token "and" >> return (fun x y -> AndExp(x, y))
let atom = (ident => (fun s -> Variable s))
       <|> (number => (fun x -> Number x))
       <|> (token "true" >> return (Bool true))
       <|> (token "false" >> return (Bool false))

let rec expr input = (chainl1 and_expr orop) input
and and_expr input = (chainl1 rop_expr andop) input
and rop_expr input = (chainl1 add_expr (ltop <|> gtop)) input
and add_expr input = (chainl1 mul_expr (addop <|> subop)) input
and mul_expr input = (chainl1 prm_expr (mulop <|> divop)) input
and prm_expr input = (parens expr <|> atom) input

let onlyTypes decl = true
let onlyTerms decl = true

let conId input = ((many alpha_num) => implode >>= function s -> return s) input

let variable input = (var >>= fun myvar -> return (Var(myvar))) input
let rec term input = (application1 <|> application2 <|> constructed <|> variable) input
and x input = (ident >>= fun myvar -> return (Var(myvar))) input
and application1 input = 
	(variable >>= fun myvar ->
	 token "[" >>
  	 term >>=  fun trm1 -> 
	 token "/x]" >>
		 return (Application(myvar, trm1))) input
and application2 input = 
	(variable >>= fun myvar ->
	 token "[" >>
	 term >>=  fun trm1 -> 
	 token "/X]" >>
		 return (Application(myvar, trm1))) input
and constructed input = 
	(token "(" >> 
	 ident >>= fun c ->
	 many term >>=  fun trms -> 
	 token ")" >> 
		 return (Constructor(c, trms))) input
(*
		 and parents input = 
	(token "(" >> 
	 term >>= fun term ->
	 token ")" >> 
		 return term) input
*)
let simple input = 
	(ident >>= fun c -> 
	return (Simple(Cov, c))) input
	
let hoas input = 
	(token "(" >> 
	 ident >>= fun c1 ->
	 token "->" >> 
	 ident >>= fun c2 ->
	 token ")" >> 
	 return (Abstraction(Cov, (c1, c2)))) input

let listEntry c input = 
	(token "(" >> 
	 token listKeyword >>
	 term >>=  fun trm -> 
	 token ")" >>
	 return (List((Cov,true), c , trm))) input

let listSelfEntry c input = 
	(token "(" >> 
	 token listSelfKeyword >>
	 term >>=  fun trm -> 
	 token ")" >>
	 return (ListSelf((Cov,true),c, trm))) input

let rec entries c input = (sep_by (typeEntry c) (token "->") => (fun l -> l)) input
and typeEntry c input =  (simple <|> hoas <|> listEntry c <|> listSelfEntry c) input

let rec premise input = (formula <|> hypothetical1 <|> hypothetical2 <|> hypotheticalSubtyping <|> generic) input
and formula input = (valueFormula <|> errorFormula <|> typingFormula <|> stepFormula <|> subtypeFormula) input
and valueFormula input = 
	(token "value" >>
 	 term >>=  fun trm -> 
	 return (Formula("value",[trm], []))) input
and typingFormula input = 
	(token "Gamma |- " >>
 	 term >>=  fun trm1 -> 
	 token ":" >>
 	 term >>=  fun trm2 -> 
	 return (Formula("typeOf",[trm1], [trm2]))) input
and errorFormula input = 
	(token "error" >>
 	 term >>=  fun trm -> 
	 return (Formula("error",[trm], []))) input
and stepFormula input = 
	(term >>=  fun trm1 -> 
	 token "-->" >>
 	 term >>=  fun trm2 -> 
	 return (Formula("step",[trm1], [trm2]))) input
and subtypeFormula input = 
	(term >>=  fun trm1 -> 
	 token "<:" >>
 	 term >>=  fun trm2 -> 
	 return (Formula("subtype",[trm1], [trm2]))) input
and hypothetical1 input = 
	(token "Gamma, x : " >>
	 term >>=  fun trm1 -> 
	 token "|-" >>
  	 term >>=  fun trm2 -> 
	 token ":" >>
  	 term >>=  fun trm3 -> 
 	 return (Hypothetical(Formula("typeOf", [Var("x")], [trm1]), Formula("typeOf", [apply trm2], [apply trm3])))) input
and hypothetical2 input = 
	(token "Gamma, X <: " >>
	 term >>=  fun trm1 -> 
	 token "|-" >>
  	 term >>=  fun trm2 -> 
	 token ":" >>
  	 term >>=  fun trm3 -> 
 	 return (Hypothetical(Formula("subtype", [Var("x")], [trm1]), Formula("typeOf", [apply trm2], [apply trm3])))) input
and hypotheticalSubtyping input = 
	(token "Gamma, X <: " >>	
	 term >>=  fun trm1 -> 
	 token "|-" >>
  	 term >>=  fun trm2 -> 
	 token "<:" >>
  	 term >>=  fun trm3 -> 
 	 return (Hypothetical(Formula("subtype", [Var("x")], [trm1]), Formula("subtype", [apply trm2], [apply trm3])))) input
and generic input = 
	(token "Gamma, X |- " 	>>
 	 term >>=  fun trm1 -> 
	 token ":" >>
 	 term >>=  fun trm2 -> 
 	 return (Generic(Formula("typeOf", [apply trm1], [apply trm2])))) input

let rec rule input = (fact <|> ruleReal) input
and fact input = 
	(formula      >>= fun f ->
	 token "." >>
	 return (Rule(formula_getRuleNameFromConclusion f,removeDuplicates (conclusion_implicitValuePremises f),f))) input
and ruleReal input = 
	(formula      >>= fun f ->
	 token "<==" >>
	 (sep_by premise (token "/\\")) >>= fun premises -> 
     token "." >>
 	 return (Rule(formula_getRuleNameFromConclusion f,removeDuplicates (premises @ conclusion_implicitValuePremises f),f))) input

let rec termGrammar input = 
	(token "(" >>
	 ident >>= fun c ->
	 many (boundGrammar <|> variable) >>=  fun trms -> 
		 token ")" >>
		 return (Constructor(c, trms))) input
and boundGrammar input = (boundExpExp <|> boundTypExp <|> boundTypTyp) input
and boundExpExp input = (token "(x)E" >> return (Bound("E"))) input
and boundTypExp input = (token "(X)E" >> return (Bound("TE"))) input
and boundTypTyp input = (token "(X)T" >> return (Bound("TT"))) input

let module_pre input = (token "module" >> ident >> token "." >> return "") input
		 
let rec tl input = (*module_pre >>*)
	(
  	 expressions >>=  fun expressions ->
   	 types >>=  fun types ->
   	 values >>=  fun values ->
   	 option [] errors >>=  fun errors ->
   	 contexts >>=  fun contexts ->
	 many rule >>=  fun rules ->
		 return (expressions, types, values, errors, contexts, rules)) input
and expressions input = 
	(token "Expression E ::= x | " >>
	(sep_by termGrammar (token "|")) >>= fun terms -> 
		return (List.map termsToSignatureTerm terms)) input
and types input = 
	(token "Type T ::= " >>
	(sep_by termGrammar (token "|")) >>= fun terms -> 
		return (List.map termsToSignatureType terms)) input
and values input = 
	(token "Value V ::= " >>
	(sep_by termGrammar (token "|")) >>= fun terms -> 
		return (List.map termsToValueRule terms)) input
and errors input = 
	(token "Error ::= " >>
	(sep_by termGrammar (token "|")) >>= fun terms -> 
		return (List.map termsToErrorRule terms)) input
and contexts input = 
	(token "Context C ::= [] | " >>
	(sep_by ctxline (token "|")) >>= fun ctxlines -> 
 	return (String.concat "\n" ctxlines )) input
and ctxline input = 
	 (token "(" >>
     ident      >>= fun c ->
	 many (token "v" <|> token "e" <|> token "C") >>=  fun args ->
	 token ")" >>
		 return (ctxTag ^ " " ^ c ^ " " ^ (String.concat " " args) ^ ".")) input

and listline input = 
	(token listInfoTag >>
   	 ident      >>= fun c ->
	 number      >>= fun value ->
	 number      >>= fun ctx -> 
     token "." >>
	 return (c, (value, ctx))) input
(*
	 and listline input = 
	(token listTag >>
   	 ident      >>= fun c ->
	 listValue      >>= fun value ->
	 listCtx      >>= fun ctx -> 
     token "." >>
	 return (c, value, ctx)) input
and listValue input = ((token "allValue" >> return All <|> token "firstValue" >> return First <|> token "noneValue" >> return NoneV) >>= fun tag -> return tag) input 
and listCtx input = ((token "sequential" >> return Sequential <|> token "parallel" >> return Parallel) >>= fun tag -> return tag) input 
*)
and subtyping input = 
	(token subsumptionTag >> 
	 token "." 
     >> return true) input
and subtyping_top input = 
	(token subtyping_top_Tag >> 
   	 ident >>= fun top ->	
	 token "." >>
	 return (Some (top))) input
and subtyping_special input = 
	(token subtyping_special_Tag >> 
   	 ident >>= fun op ->	
	 token ":" >>
 	 ((rule >>= fun rule -> return ((op, rule))) <|> (token widthKeyword >> token "." >> return (op ^ "T", (subtyping_widthRule op)))) >>= fun pair -> 
   	 (* rule >>= fun rule -> *)
	 (* return (op, rule)) input *)
 	return pair) input
and	variance input = 
	(( (token contravariantTag >> return Contra) <|> 
   	   (token invariantTag >> return Inv) <|> 
	   (token recursiveTag >> return Rec)) >>=  fun tag ->
	ident >>= fun c ->
	number >>=  fun n ->
	token "." >>
	return ((c,n-1), tag)) input
 
let sig_pre input = (token "sig" >> ident >> token "." >> return "") input
let kindDecl input = (token "kind" >> ident >> token "type" >> token "." >> return "") input

let rec sigg input = 
	(sig_pre >> 
(*   	 many kindDecl >>= fun ignore -> *)
	 many kindDecl >>= fun ignore -> 
	 many declaration >>= fun decls ->
	 return (List.map decl_remove_lastArg (List.filter onlyTypes decls), List.map convertToTerm (List.filter onlyTerms decls))) input
and declaration input = 
	(token "type" >>
	 ident      >>= fun c ->
	 entries c >>= fun args ->
	 token "." >>
	 return (DeclType(c,args))) input	 
and onlyTypes typeDecl = entry_toKindProduced (last (type_getArguments typeDecl)) = "typ"
and onlyTerms typeDecl = entry_toKindProduced (last (type_getArguments typeDecl)) = "term"
and convertToTerm typeDecl = DeclTrm(type_getOperator typeDecl, [], [], remove_last (type_getArguments typeDecl))
and decl_remove_lastArg typeDecl = DeclType(type_getOperator typeDecl, remove_last (type_getArguments typeDecl))
	 
(*let sigg input = 
	(many sigtype >>=  fun sigTypes -> 
	 many sigterm >>=  fun sigTerms ->
		 return (sigTypes, sigTerms)) input
DeclType("",[])DeclTrm("", [], [], [])
*)

let wrap_tl = tl << (spaces << eof ())
let wrap_sig = sigg << (spaces << eof ())
let parse_sig input = parse wrap_sig input
let parse_tl input = parse wrap_tl input

let readFromLanToRulesAndTags fileName = 
	let mysplitEndInStream line = Str.string_after line (1 + (Str.search_forward (Str.regexp_string ":") line 0)) in  
	let myParseRule toParse =  match (rule (LazyStream.of_string  toParse)) with | None -> raise(Failure("Syntax for user-defined subtyping in : " ^ fileName ^ toParse)) | Some pair -> fst pair in  (* Recall that parsing return an option with a pair (element, stream)  *)
	let languageName = fileName in  
	let fileName = "./repo/" ^ fileName in 
	let filee = open_in (fileName ^ ".lan") in 
	let forRules = open_out (fileName ^ ".rules") in 
	let forTags = open_out (fileName ^ ".tags") in 
		let rec dico_rec () =
		    (try
				let line = input_line filee in 
				      (match (String.contains line '%') with 
					  | true -> (match startsWith line subtyping_special_Tag with 
						  			| true -> output_string forTags (List.hd (Str.split (Str.regexp_string ":") line)) ; output_string forTags ":"; output_string forTags (generateRule (myParseRule (mysplitEndInStream line))) ; output_string forTags "\n";
				  					| false ->  output_string forTags line; output_string forTags "\n";);
					  | false -> output_string forRules line; output_string forRules "\n";);
				      dico_rec();
		    with End_of_file -> close_in filee; close_out forRules; close_out forTags;)
		in dico_rec();;

let addTags mylan fileName = 
	let languageName = fileName in 
	let fileName = "./repo/" ^ fileName in 
	let mytags = open_in (fileName ^ ".tags") in 
		let rec dico_rec () =
		    (try
				let line = input_line mytags in 
				      (output_string mylan line; output_string mylan "\n";);
				      dico_rec();
		    with End_of_file -> close_in mytags;) 
		in dico_rec();;

let createSig languageName mysig expressions types = output_string mysig (generateSigPreambleFROM_LAN languageName); output_string mysig (String.concat "\n" types); output_string mysig "\n\n"; output_string mysig (String.concat "\n" expressions); close_out mysig;;
let createMod languageName mylan values errors contexts rules = output_string mylan (generateModuleFromLang languageName rules); output_string mylan (generateRules values); output_string mylan (generateRules errors); output_string mylan "\n\n"; output_string mylan contexts; output_string mylan "\n"; addTags mylan languageName; close_out mylan;;

let parseFileLan fileName = 
	readFromLanToRulesAndTags fileName;
	let languageName = fileName in 
	let fileName = "./repo/" ^ fileName in 
	let mymod = open_in (fileName ^ ".rules") in 
	let mysig = open_out (fileName ^ ".sig") in 
	let mylan = open_out (fileName ^ ".mod") in 
	let src_mod = LazyStream.of_channel mymod in
			match parse_tl src_mod with 
    		| None -> raise(Failure("Syntax Error in Language: " ^ fileName))
			| Some (expressions, types, values, errors, contexts, rules) -> close_in mymod; createSig languageName mysig expressions types; createMod languageName mylan values errors contexts rules; Sys.remove (fileName ^ ".rules"); Sys.remove (fileName ^ ".tags");
					