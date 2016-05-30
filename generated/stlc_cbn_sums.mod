module stlc_cbn_sums.

typeOf (inr E) (sum T1 T2) :- typeOf E T2.

typeOf (inl E) (sum T1 T2) :- typeOf E T1.

typeOf (abs R T1) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (case EE R1 R2) T :- typeOf EE (sum T1 T2), (pi x\ typeOf x T1 => typeOf (R1 x) T), (pi x\ typeOf x T2 => typeOf (R2 x) T).

step (case (inl EE) R1 R2) (R1 EE).

step (case (inr EE) R1 R2) (R2 EE).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs R T) E) (R E).

value (inr E1) :- value E1.

value (inl E1) :- value E1.

value (abs R1 T2).

step (inr E1) (inr E1') :- step E1 E1'.

step (inl E1) (inl E1') :- step E1 E1'.

step (case E1 R2 R3) (case E1' R2 R3) :- step E1 E1'.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.
