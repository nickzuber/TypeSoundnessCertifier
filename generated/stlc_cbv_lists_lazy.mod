module stlc_cbv_lists_lazy.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (emptyList ) (list T).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T1 R) V) (R V) :- value V.

typeOf (head E) T :- typeOf E (list T).

step (head (emptyList )) (myError ).

step (head (cons E1 E2)) E1.

typeOf (tail E) (list T) :- typeOf E (list T).

step (tail (emptyList )) (myError ).

step (tail (cons E1 E2)) E2.

value (abs T1 R2).

value (cons E1 E2).

value (emptyList ).

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2', value E1.

step (head E1) (head E1') :- step E1 E1'.

step (tail E1) (tail E1') :- step E1 E1'.

error (myError ).

typeOf (myError ) T.

step (app E1 E2) E1 :- error E1.

step (app E1 E2) E2 :- error E2.

step (head E1) E1 :- error E1.

step (tail E1) E1 :- error E1.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.

