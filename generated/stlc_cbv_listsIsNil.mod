module stlc_cbv_listsIsNil.

typeOf (ff ) (bool ).

typeOf (tt ) (bool ).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (emptyList ) (list T).

typeOf (abs R T1) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

typeOf (isnil E) (bool ) :- typeOf E (list T).

step (isnil (emptyList )) (tt ).

step (isnil (cons E1 E2)) (ff ).

typeOf (tail E) (list T) :- typeOf E (list T).

step (tail (emptyList )) (myError ).

step (tail (cons E1 E2)) E2.

typeOf (head E) T :- typeOf E (list T).

step (head (emptyList )) (myError ).

step (head (cons E1 E2)) E1.

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs R T) V) (R V) :- value V.

value (ff ).

value (tt ).

value (cons E1 E2) :- value E1, value E2.

value (emptyList ).

value (abs R1 T2).

step (cons E1 E2) (cons E1' E2) :- step E1 E1'.

step (cons E1 E2) (cons E1 E2') :- step E2 E2', value E1.

step (if E1 E2 E3) (if E1' E2 E3) :- step E1 E1'.

step (isnil E1) (isnil E1') :- step E1 E1'.

step (tail E1) (tail E1') :- step E1 E1'.

step (head E1) (head E1') :- step E1 E1'.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2', value E1.

error (myError ).

typeOf (myError ) T.

step (cons E1 E2) E1 :- error E1.

step (cons E1 E2) E2 :- error E2.

step (if E1 E2 E3) E1 :- error E1.

step (isnil E1) E1 :- error E1.

step (tail E1) E1 :- error E1.

step (head E1) E1 :- error E1.

step (app E1 E2) E1 :- error E1.

step (app E1 E2) E2 :- error E2.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.
