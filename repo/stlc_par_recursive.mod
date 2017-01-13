module stlc_par.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (fold E R) (mu R) :- typeOf E (R (mu R)).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T R) E) (R E).

typeOf (unfold E) (R (mu R)) :- typeOf E (mu R).

step (unfold (fold V R)) V :- value V.

value (abs T1 R2).

value (fold E1 U2) :- value E1.


% context app E e.
% context app e E.
% context fold E e.
% context unfold E.

