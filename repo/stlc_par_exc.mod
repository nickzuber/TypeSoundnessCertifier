module stlc_par_exc.

typeOf (abs R T1) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (excValue ) (excType ).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs R T) E) (R E).

typeOf (try E1 E2) T :- typeOf E1 T, typeOf E2 (arrow (excType ) T).

step (try E1 E2) E1 :- value E1.

step (try (raise E1) E2) (app E2 E1).

value (abs R1 T2).

value (excValue ).

error (raise E1) :- value E1.

typeOf (raise E) T :- typeOf E (excType ).



% context app C e.
% context app e C.
% context try C e.
% context raise C.