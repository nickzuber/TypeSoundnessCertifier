module mycalculus.

typeOf (abs R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (tt ) (bool ).

typeOf (ff ) (bool ).

typeOf (absT R2) (all R) :- (pi x\ typeOf (R2 x) (R x)).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

typeOf (appT E X) (R X) :- typeOf E (all R).

step (app (abs R) APPLIED) (R APPLIED).

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

step (appT (absT R2) X) (R2 X).

value (abs E1).

value (tt ).

value (ff ).

value (absT E1).

termPred (abs E1).

termPred (tt ).

termPred (ff ).

termPred (absT E1).

termPred (app E1 E2) :- termPred E1, termPred E2.

termPred (if E1 E2 E3) :- termPred E1, termPred E2, termPred E3.

termPred (appT E1 X1) :- termPred E1.

nonvalue (app E1 E2) :- termPred E1, termPred E2.

nonvalue (if E1 E2 E3) :- termPred E1, termPred E2, termPred E3.

nonvalue (appT E1 X1) :- termPred E1.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (if E1 E2 E3) (if E1' E2 E3) :- step E1 E1'.

step (if E1 E2 E3) (if E1 E2' E3) :- step E2 E2'.

step (if E1 E2 E3) (if E1 E2 E3') :- step E3 E3'.

step (appT E1 X1) (appT E1' X1) :- step E1 E1'.
