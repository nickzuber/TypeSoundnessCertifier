module stlc_par_letrecWithType.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T1 R) E) (R E).

typeOf (letrec T1 R1 R2) T2 :- (pi x\ typeOf x T1 => typeOf (R1 x) T1), (pi x\ typeOf x T1 => typeOf (R2 x) T2).

step (letrec T R1 R2) (let (fix (abs T R1)) R2).

typeOf (let E R) T2 :- typeOf E T1, (pi x\ typeOf x T1 => typeOf (R x) T2).

step (let V R) (R V) :- value V.

typeOf (fix E) T :- typeOf E (arrow T T).

step (fix V) (app V (fix V)) :- value V.

value (abs T1 R2).

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2'.

step (let E1 R2) (let E1' R2) :- step E1 E1'.

step (fix E1) (fix E1') :- step E1 E1'.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.

