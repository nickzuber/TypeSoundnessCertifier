module stlc_lists.

typeOf (abs R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (emptyList ) (list T).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

typeOf (head E) T :- typeOf E (list T).

typeOf (myError ) T.

step (app (abs R) EE) (R EE).

step (head (emptyList )) (myError ).

step (head (cons E1 E2)) E1.

value (abs R1).

value (emptyList ).

value (cons E1 E2).

error (myError ).

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (head E1) (head E1') :- step E1 E1'.

step (app E1 E2) E1 :- error E1.

step (head E1) E1 :- error E1.
