module stlc_cbv_unitt.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (unit ) (unitType ).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T R) V) (R V) :- value V.

value (abs T1 R2).

value (unit ).



% context app C e.
% context app v C.