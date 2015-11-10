module fullFledged_par.

typeOf (abs R T1) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (tt ) (bool ).

typeOf (ff ) (bool ).

typeOf (emptyList ) (list T).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (absT R2) (all R) :- (pi x\ typeOf (R2 x) (R x)).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

typeOf (head E) T :- typeOf E (list T).

typeOf (tail E) (list T) :- typeOf E (list T).

typeOf (isnil E) (bool ) :- typeOf E (list T).

typeOf (appT E X) (R X) :- typeOf E (all R).

typeOf (let E R) T2 :- typeOf E T1, (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (myError ) T.

step (app (abs R T) EE) (R EE).

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

step (head (emptyList )) (myError ).

step (head (cons E1 E2)) E1.

step (tail (emptyList )) (myError ).

step (tail (cons E1 E2)) E2.

step (isnil (emptyList )) (tt ).

step (isnil (cons E1 E2)) (ff ).

step (appT (absT R2) X) (R2 X).

step (let V R) (R V) :- value V.

value (abs R1 T2).

value (tt ).

value (ff ).

value (emptyList ).

value (cons E1 E2).

value (absT R1).

error (myError ).

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2', value E1.

step (if E1 E2 E3) (if E1' E2 E3) :- step E1 E1'.

step (if E1 E2 E3) (if E1 E2' E3) :- step E2 E2', value E1.

step (if E1 E2 E3) (if E1 E2 E3') :- step E3 E3', value E1, value E2.

step (head E1) (head E1') :- step E1 E1'.

step (tail E1) (tail E1') :- step E1 E1'.

step (isnil E1) (isnil E1') :- step E1 E1'.

step (appT E1 T2) (appT E1' T2) :- step E1 E1'.

step (let E1 R2) (let E1' R2) :- step E1 E1'.

step (app E1 E2) E1 :- error E1.

step (app E1 E2) E2 :- error E2.

step (if E1 E2 E3) E1 :- error E1.

step (if E1 E2 E3) E2 :- error E2.

step (if E1 E2 E3) E3 :- error E3.

step (head E1) E1 :- error E1.

step (tail E1) E1 :- error E1.

step (isnil E1) E1 :- error E1.

step (appT E1 T2) E1 :- error E1.

step (let E1 R2) E1 :- error E1.
