module stlc_cbv_tuples_plain.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (tuple5 E1 E2 E3 E4 E5) (times5 T1 T2 T3 T4 T5) :- typeOf E1 T1, typeOf E2 T2, typeOf E3 T3, typeOf E4 T4, typeOf E5 T5.

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T R) V) (R V) :- value V.

typeOf (select1 E) T1 :- typeOf E (times5 T1 T2 T3 T4 T5).

step (select1 (tuple5 E1 E2 E3 E4 E5)) E1.

typeOf (select2 E) T2 :- typeOf E (times5 T1 T2 T3 T4 T5).

step (select2 (tuple5 E1 E2 E3 E4 E5)) E2.

typeOf (select3 E) T3 :- typeOf E (times5 T1 T2 T3 T4 T5).

step (select3 (tuple5 E1 E2 E3 E4 E5)) E3.

typeOf (select4 E) T4 :- typeOf E (times5 T1 T2 T3 T4 T5).

step (select4 (tuple5 E1 E2 E3 E4 E5)) E4.

typeOf (select5 E) T5 :- typeOf E (times5 T1 T2 T3 T4 T5).

step (select5 (tuple5 E1 E2 E3 E4 E5)) E5.

value (abs T1 R2).

value (tuple5 E1 E2 E3 E4 E5) :- value E1, value E2, value E3, value E4, value E5.


% context tuple5 C e e e e.
% context tuple5 v C e e e.
% context tuple5 v v C e e.
% context tuple5 v v v C e.
% context tuple5 v v v v C.
% context app C e.
% context app v C.
% context select1 C.
% context select2 C.
% context select3 C.
% context select4 C.
% context select5 C.