module stlc_cbn.

typeOf (abs R T1) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs R T) E) (R E).

value (abs R1 T2).

step (app E1 E2) (app E1' E2) :- step E1 E1'.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.
