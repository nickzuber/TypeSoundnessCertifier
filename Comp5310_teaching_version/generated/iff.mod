module iff.

typeOf (ff ) (bool ).

typeOf (tt ) (bool ).

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

value (ff ).

value (tt ).

step (if E1 E2 E3) (if E1' E2 E3) :- step E1 E1'.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.

