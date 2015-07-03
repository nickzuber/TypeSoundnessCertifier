module mycalculus.

typeOf (abs R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (tt ) (bool ).

typeOf (ff ) (bool ).

typeOf (pair E1 E2) (times T1 T2) :- typeOf E1 T1, typeOf E2 T2.

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

typeOf (fst E) T1 :- typeOf E (times T1 T2).

typeOf (snd E) T2 :- typeOf E (times T1 T2).

step (app (abs R) APPLIED) (R APPLIED).

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

step (fst (pair E1 E2)) E1.

step (snd (pair E1 E2)) E2.

value (abs E1).

value (tt ).

value (ff ).

value (pair E1 E2) :- value E1, value E2.

termPred (abs E1).

termPred (tt ).

termPred (ff ).

termPred (pair E1 E2) :- termPred E1, termPred E2.

termPred (app E1 E2) :- termPred E1, termPred E2.

termPred (if E1 E2 E3) :- termPred E1, termPred E2, termPred E3.

termPred (fst E1) :- termPred E1.

termPred (snd E1) :- termPred E1.

nonvalue (pair E1 E2) :- termPred E1, termPred E2, nonvalue E1.

nonvalue (pair E1 E2) :- termPred E1, termPred E2, nonvalue E2.

nonvalue (app E1 E2) :- termPred E1, termPred E2.

nonvalue (if E1 E2 E3) :- termPred E1, termPred E2, termPred E3.

nonvalue (fst E1) :- termPred E1.

nonvalue (snd E1) :- termPred E1.

step (pair E1 E2) (pair E1' E2) :- step E1 E1'.

step (pair E1 E2) (pair E1 E2') :- step E2 E2'.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2'.

step (if E1 E2 E3) (if E1' E2 E3) :- step E1 E1'.

step (if E1 E2 E3) (if E1 E2' E3) :- step E2 E2'.

step (if E1 E2 E3) (if E1 E2 E3') :- step E3 E3'.

step (fst E1) (fst E1') :- step E1 E1'.

step (snd E1) (snd E1') :- step E1 E1'.
