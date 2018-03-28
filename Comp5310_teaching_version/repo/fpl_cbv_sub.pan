Expression E ::= x | (abs T (x)E) | (app E E) | (zero) | (succ E) | (pred E) | (tt) | (ff) | (if E E E) | (pair E E) | (fst E) | (snd E) | (inr E) | (inl E) | (case E (x)E (x)E) | (emptyList) | (cons E E) | (head E) | (tail E) | (absT (X)E) | (appT E T) | (letrec T (x)E (x)E) | (fix E) | (try E E) | (raise E) | (topObj)
Type T ::= (top) | (int) | (bool) | (arrow T T) | (times T T) | (sum T T) | (list T) | (all (X)T)
Value V ::= (abs T R) | (inl V) | (inr V) | (pair V1 V2) | (zero ) | (succ V) | (tt) | (ff) | (emptyList) | (cons V1 V2) | (absT E)
Error ::= (raise V)
Context C ::= [] | (app C e) | (app v C) | (inl C) | (inr C) | (fst C) | (snd C) | (pair C e) | (pair v C) | (case C e e) | (succ C) | (pred C) | (if C e e) | (head C) | (tail C) | (cons C e) | (cons v C) | (raise C) | (try C e) | (appT C e) | (fix C)

Gamma |- (topObj ) : (top ).

Gamma |- (abs T1 R) : (arrow T1 T2) <== Gamma, x : T1 |- R : T2.

Gamma |- (zero ) : (int ).

Gamma |- (succ E) : (int ) <== Gamma |- E : (int ).

Gamma |- (tt ) : (bool ).

Gamma |- (ff ) : (bool ).

Gamma |- (pair E1 E2) : (times T1 T2) <== Gamma |- E1 : T1 /\ Gamma |- E2 : T2.

Gamma |- (inl E) : (sum T1 T2) <== Gamma |- E : T1.

Gamma |- (inr E) : (sum T1 T2) <== Gamma |- E : T2.

Gamma |- (emptyList ) : (list T).

Gamma |- (cons E1 E2) : (list T) <== Gamma |- E1 : T /\ Gamma |- E2 : (list T).

Gamma |- (absT R2) : (all R) <== Gamma, X |- R2 : R.

Gamma |- (app E1 E2) : T2 <== Gamma |- E1 : (arrow T1 T2) /\ Gamma |- E2 : T1.

(app (abs T1 R) V) --> R[V/x] <== value V.

Gamma |- (pred E) : (int) <== Gamma |- E : (int).

(pred (zero )) --> (raise (zero )).

(pred (succ V)) --> V.

Gamma |- (if E1 E2 E3) : T <== Gamma |- E1 : (bool ) /\ Gamma |- E2 : T /\ Gamma |- E3 : T.

(if (tt ) E1 E2) --> E1.

(if (ff ) E1 E2) --> E2.

Gamma |- (fst E) : T1 <== Gamma |- E : (times T1 T2).

(fst (pair E1 E2)) --> E1.

Gamma |- (snd E) : T2 <== Gamma |- E : (times T1 T2).

(snd (pair E1 E2)) --> E2.

Gamma |- (case EE R1 R2) : T <== Gamma |- EE : (sum T1 T2) /\ Gamma, x : T1 |- R1 : T /\ Gamma, x : T2 |- R2 : T.

(case (inl E) R1 R2) --> R1[E/x] <== value E.

(case (inr E) R1 R2) --> R2[E/x] <== value E.

Gamma |- (head E) : T <== Gamma |- E : (list T).

(head (emptyList )) --> (raise (zero )).

(head (cons E1 E2)) --> E1.

Gamma |- (tail E) : (list T) <== Gamma |- E : (list T).

(tail (emptyList )) --> (raise (succ (zero ))).

(tail (cons E1 E2)) --> E2.

Gamma |- (appT E X) : R'[X/x] <== Gamma |- E : (all R').

(appT (absT R2) X) --> R2[X/x].

Gamma |- (fix E) : T <== Gamma |- E : (arrow T T).

(fix E) --> (app E (fix E)) <== value E.

Gamma |- (letrec T1 R1 R2) : T2 <== Gamma, x : T1 |- R1 : T1 /\ Gamma, x : T1 |- R2 : T2.

(letrec T1 R1 R2) --> R2[(fix (abs T1 R1))/x].

Gamma |- (try E1 E2) : T <== Gamma |- E1 : T /\ Gamma |- E2 : (arrow (int ) T).

(try E1 E2) --> E1 <== value E1.

(try (raise E1) E2) --> (app E2 E1).

Gamma |- (raise E) : T <== Gamma |- E : (int ).


% declarative-subtyping.
% subtyping-top top.
% contravariant arrow 1.
