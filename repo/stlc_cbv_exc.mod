module stlc_cbv_exc.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (excValue ) (excType ).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T R) V) (R V) :- value V.

typeOf (try E1 E2) T :- typeOf E1 T, typeOf E2 (arrow (excType ) T).

step (try E1 E2) E1 :- value E1.

step (try (raise E1) E2) (app E2 E1).

value (abs T1 R2).

value (excValue ).

error (raise E1) :- value E1.

typeOf (raise E) T :- typeOf E (excType ).



% context app E e.
% context app v E.
% context try E e.
% context raise E.
