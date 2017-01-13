module iff.

typeOf (tt ) (bool ).

typeOf (ff ) (bool ).

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

value (tt ).

value (ff ).



% context if E e e.
