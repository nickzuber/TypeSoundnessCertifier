module stlc_cbn_pairs_onlysnd.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (pair E1 E2) (times T1 T2) :- typeOf E1 T1, typeOf E2 T2.

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T R) E) (R E).

typeOf (fst E) T1 :- typeOf E (times T1 T2).

step (fst (pair E1 E2)) E1.

typeOf (snd E) T2 :- typeOf E (times T1 T2).

step (snd (pair E1 E2)) E2.

value (abs T1 R2).

value (pair E1 E2) :- value E2.


% context pair e E.
% context app E e.
% context fst E.
% context snd E.
