module pairs_plain.

typeOf (pair E1 E2) (times T1 T2) :- typeOf E1 T1, typeOf E2 T2.

typeOf (fst E) T1 :- typeOf E (times T1 T2).

step (fst (pair E1 E2)) E1.

typeOf (snd E) T2 :- typeOf E (times T1 T2).

step (snd (pair E1 E2)) E2.

value (pair E1 E2) :- value E1, value E2.

% context pair C v.
% context pair e C.
% context fst C.
% context snd C.