Expression E ::= x | (abs T (x)E) | (app E E) | (absT T (X)E) | (appT E T) | (topObj)
Type T ::= (top) | (arrow T T) | (all T (X)T)
Value V ::= (abs T R) | (absT T E)
Context C ::= [] | (app C e) | (app v C) | (appT C e) 

Gamma |- (abs T1 R) : (arrow T1 T2) <== Gamma, x : T1 |- R : T2.

Gamma |- (absT T1 R2) : (all T1 R) <== Gamma, X <: T1 |- R2 : R.

Gamma |- (topObj ) : (top ).

Gamma |- (app E1 E2) : T2 <== Gamma |- E1 : (arrow T1' T2) /\ Gamma |- E2 : T1'.

(app (abs T1 R) V) --> R[V/x] <== value V.

Gamma |- (appT E X) : R'[X/x] <== Gamma |- E : (all T2 R') /\ X <: T2.

(appT (absT T1 R2) X) --> R2[X/x].

% declarative-subtyping.
% subtyping-top top.
% contravariant arrow 1.
% subtyping-for all: (all T R) <: (all T' R') <== T' <: T /\ Gamma, X <: T' |- R <: R'.
