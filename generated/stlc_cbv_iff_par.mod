module stlc_cbv_iff_par.

typeOf (ff ) (bool ).

typeOf (tt ) (bool ).

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T R) V) (R V) :- value V.

value (ff ).

value (tt ).

value (abs T1 R2).

step (if E1 E2 E3) (if E1' E2 E3) :- step E1 E1'.

step (if E1 E2 E3) (if E1 E2' E3) :- step E2 E2'.

step (if E1 E2 E3) (if E1 E2 E3') :- step E3 E3'.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2', value E1.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.
