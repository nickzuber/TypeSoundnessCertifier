module pairs_rightToLeft.

typeOf (pair E1 E2) (times T1 T2) :- typeOf E1 T1, typeOf E2 T2.

typeOf (fst E) T1 :- typeOf E (times T1 T2).

step (fst (pair E1 E2)) E1.

typeOf (snd E) T2 :- typeOf E (times T1 T2).

step (snd (pair E1 E2)) E2.

value (pair E1 E2) :- value E1, value E2.

step (pair E1 E2) (pair E1' E2) :- step E1 E1', value E2.

step (pair E1 E2) (pair E1 E2') :- step E2 E2'.

step (fst E1) (fst E1') :- step E1 E1'.

step (snd E1) (snd E1') :- step E1 E1'.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.

