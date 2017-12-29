module stlc_cbn_recursive.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (fold E R) (mu R) :- typeOf E (R (mu R)).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T1 R) E) (R E).

typeOf (unfold E') (R (mu R)) :- typeOf E' (mu R).

step (unfold (fold E R)) E :- value E.

value (abs T1 R2).

value (fold E1 U2) :- value E1.

step (fold E1 U2) (fold E1' U2) :- step E1 E1'.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (unfold E1) (unfold E1') :- step E1 E1'.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.

