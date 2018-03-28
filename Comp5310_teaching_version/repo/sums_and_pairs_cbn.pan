Expression E ::= x | (abs T (x)E) | (app E E) | (pair E E) | (fst E) | (snd E) | (inr E) | (inl E) | (case E (x)E (x)E)
Type T ::= (arrow T T) | (times T T) | (sum T T)
Value V ::= (abs T E) | (inl V) | (inr V) | (pair V V)
Context C ::= [] | (app C e) | (inl C) | (inr C) | (fst C) | (snd C) | (pair C e) | (pair v C) | (case C e e)

Gamma |- (abs T1 R) : (arrow T1 T2) <== Gamma, x : T1 |- R : T2.

Gamma |- (inl E) : (sum T1 T2) <== Gamma |- E : T1.

Gamma |- (inr E) : (sum T1 T2) <== Gamma |- E : T2.

Gamma |- (pair E1 E2) : (times T1 T2) <== Gamma |- E1 : T1 /\ Gamma |- E2 : T2.

Gamma |- (app E1 E2) : T2 <== Gamma |- E1 : (arrow T1 T2) /\ Gamma |- E2 : T1.

(app (abs T R) E) --> R[E/x].

Gamma |- (case EE R1 R2) : T <== Gamma |- EE : (sum T1 T2) /\ Gamma, x : T1 |- R1 : T /\ Gamma, x : T2 |- R2 : T.

(case (inl V) R1 R2) --> R1[V/x] <== value V.

(case (inr V) R1 R2) --> R2[V/x] <== value V.

Gamma |- (fst E) : T1 <== Gamma |- E : (times T1 T2).

(fst (pair E1 E2)) --> E1.

Gamma |- (snd E) : T2 <== Gamma |- E : (times T1 T2).

(snd (pair E1 E2)) --> E2.

