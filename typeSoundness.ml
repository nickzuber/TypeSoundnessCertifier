
(*
	The proof for type soundness is *mostly* language independent when the other proofs are established.
	So we can simply statically print the Abella code rather than generate a representation for it. 
	This will be similar for other proof assistants: we glimpse that the proof code can be statically printed.
	The only information to know is whether the language has errors or not because the statement changes accordingly.	
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
