
let typesoundnessProof = 
"Theorem type_soundness : forall E E' T, {typeOf E T} -> {nstep E E'} -> progresses E'. \n
induction on 2. intros Main NStep. Step1 : case NStep. \n
backchain progress. \n
TypeOfE2: apply preservation to Main Step1. backchain IH with E = E2.\n"
