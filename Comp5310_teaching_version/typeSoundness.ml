
(*
	The proof for type soundness is basically language independent when the other proofs are established.
	Exceptionally, here we simply print out proof code, rather than representing the proof. 
	We could have just as easily represent the proof. 
    Example of representing the proof + compile are extensive in other source files such as progress.ml, preservaion.ml, subtyping.ml, and many others. 
*)

let typesoundnessProof err = 
	let errClause = if err then "\/ {error E'} " else "" in 
	let cases = if err then "search. search. search." else "search. search." in  
	
"Theorem preservation_nstep : forall Exp Exp' Typ, {typeOf Exp Typ} -> {nstep Exp Exp'} -> {typeOf Exp' Typ}. 
induction on 2. intros. case H2. search. 
apply preservation to H1 H3. apply IH to H5 H4. search. 
Theorem type_soundness : forall E E' T, {typeOf E T} -> {nstep E E'} -> 
({value E'} /\\ {typeOf E' T}) " ^ errClause ^ "\/ exists E'', {step E' E''}.
induction on 2. intros Main NStep. 
TypeOfEPrime : apply preservation_nstep to Main NStep. Step1 : case NStep. 
Progress : apply progress to TypeOfEPrime.
case Progress. " 
^ cases ^
"\nTypeOfE2: apply preservation to Main Step1. backchain IH with E = E2.\n"


