module itlc_cbv_fix.

typeOf (abs R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs R) EE) (R EE) :- value EE.

typeOf (fix E) T :- typeOf E (arrow T T).

step (fix V) (app V (fix V)) :- value V.

value (abs R1).

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2', value E1.

step (fix E1) (fix E1') :- step E1 E1'.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.

