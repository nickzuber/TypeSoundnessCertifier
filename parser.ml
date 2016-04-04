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

open TypedLanguage

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
let reserved = ["sig" ; "kind" ; "module" ; "(pi x\\ typeOf" ; "=> typeOf" ; ":-" ; "." ; "," ; "(" ; ")" ; "type" ; "->" ; ctxTag ; "e" ; "v" ; "C"]

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

let simple input = 
	(ident >>= fun c -> 
	return (Simple(c))) input
	
let hoas input = 
	(token "(" >> 
	 ident >>= fun c1 ->
	 token "->" >> 
	 ident >>= fun c2 ->
	 token ")" >> 
	 return (Abstraction(c1, c2))) input


let rec entries input = (sep_by typeEntry (token "->") => (fun l -> l)) input
and typeEntry input =  (simple <|> hoas) input

let rec term input = (variable <|> x <|> application <|> constructed) input
and variable input = (var >>= fun myvar -> return (Var(myvar))) input
and x input = (ident >>= fun myvar -> return (Var(myvar))) input
and application input = 
	(token "(" >>
	 variable >>= fun myvar ->
	 term >>=  fun trm -> 
	 token ")" >>
		 return (Application(myvar, trm))) input
and constructed input = 
	(token "(" >>
	 ident >>= fun c ->
	 many term >>=  fun trms -> 
	 token ")" >>
		 return (Constructor(c, trms))) input

let rec premise input = (formula <|> hypothetical <|> generic) input
and formula input = 
	(ident      >>= fun pred ->
	 many term >>=  fun trms -> 
	 return (Formula(pred,[List.hd trms], List.tl trms))) input
and hypothetical input = 
	(token "(pi x\\ typeOf" 	>>
	 ident >>
  	 term >>=  fun trm1 -> 
	 token "=> typeOf" >>
  	 term >>=  fun trm2 -> 
  	 term >>=  fun trm3 -> 
	 token ")" >>	 
 	 return (Hypothetical(trm1, trm2, trm3))) input
and generic input = 
	(token "(pi x\\ typeOf" 	>>
 	 term >>=  fun trm1 -> 
 	 term >>=  fun trm2 -> 
     token ")" >>
 	 return (Generic(trm1, trm2))) input

let rec rule input = (fact <|> ruleReal) input
and fact input = 
	(formula      >>= fun f ->
	 token "." >>
	 return (Rule(formula_getRuleNameFromConclusion f,[],f))) input
and ruleReal input = 
	(formula      >>= fun f ->
	 token ":-" >>
	 (sep_by premise (token ",")) >>= fun premises -> 
     token "." >>
 	 return (Rule(formula_getRuleNameFromConclusion f,premises,f))) input

let module_pre input = (token "module" >> ident >> token "." >> return "") input
		 
let rec tl input = 
	(module_pre >>
	 many rule >>=  fun rules ->
	 many ctxline >>=  fun ctxs ->
		return ((TypedLanguage([], [], rules)), ctxs)) input
and ctxline input = 
	(token ctxTag >>
	 ident      >>= fun c ->
	 many (token "v" <|> token "e" <|> token "C") >>=  fun args ->
     token "." >>
	 return (c, args)) input

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
	 entries >>= fun args ->
	 token "." >>
	 return (DeclType(c,args))) input	 
and onlyTypes typeDecl = (last (type_getArguments typeDecl)) = Simple("typ")
and onlyTerms typeDecl = (last (type_getArguments typeDecl)) = Simple("term")
and convertToTerm typeDecl = DeclTrm(type_getOperator typeDecl, [], [], remove_last (type_getArguments typeDecl))
and decl_remove_lastArg typeDecl = DeclType(type_getOperator typeDecl, remove_last (type_getArguments typeDecl))
	 
(*let sigg input = 
	(many sigtype >>=  fun sigTypes -> 
	 many sigterm >>=  fun sigTerms ->
		 return (sigTypes, sigTerms)) input
DeclType("",[])DeclTrm("", [], [], [])
*)

let insertCtx ctxlines termDecl = match termDecl with DeclTrm(c, _, _, arguments) ->
	let ctxs = List.map snd (List.filter (fun pair -> fst pair = c) ctxlines) in 
	let toNumbers = List.map (fun ll -> List.mapi (fun i -> fun letter -> if letter = "v" || letter = "C" then i+1 else -1) ll) ctxs in 
	let removeOther = List.map (fun ll -> List.sort compare (List.filter (fun n -> n > 0) ll)) toNumbers in 
	let valpositions = List.map last removeOther in 
	let contexts = List.map (fun ll -> (last ll, remove_last ll)) removeOther in 
	 DeclTrm(c, valpositions, contexts, arguments)
	 
let wrap_tl = tl << (spaces << eof ())
let wrap_sig = sigg << (spaces << eof ())
let parse_sig input = parse wrap_sig input
let parse_tl input = parse wrap_tl input

let parseFile fileName = 
	let mysig = open_in ("./repo/" ^ fileName ^ ".sig") in 
	let mymod = open_in ("./repo/" ^ fileName ^ ".mod") in 
	let src_sig = LazyStream.of_channel mysig in
	match parse_sig src_sig with 
    | None -> raise(Failure("Syntax Error in Signature, file: " ^ fileName))
    | Some (sigTypes, sigTerms) -> 
		(let src_mod = LazyStream.of_channel mymod in
			match parse_tl src_mod with 
    		| None -> raise(Failure("Syntax Error in Module: " ^ fileName))
			| Some (TypedLanguage(_, _, rules), ctxs) -> close_in mysig; close_in mymod; TypedLanguage(sigTypes, List.map (insertCtx ctxs) sigTerms, rules))
		
		

(*
			| Some (TypedLanguage(_, _, rules), ctxs) -> TypedLanguage(sigTypes, List.map (insertCtx ctxs) sigTerms, rules))
			
let parse_tl input = parse tl input

let () =
  let src = LazyStream.of_channel stdin in
  match parse_tl src with
  | None -> raise Syntax_error
  | Some prog ->
      let env = Hashtbl.create 16 in
      eval prog env;
      let pairs = Hashtbl.fold (fun k v acc -> (k, v) :: acc) env [] in
      let pairs' = List.sort (fun (k1, _) (k2, _) -> compare k1 k2) pairs in
      List.iter (fun (k, v) -> Printf.printf "%s %d\n" k v) pairs'
*)