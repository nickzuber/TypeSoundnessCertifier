module foralll.

typeOf (absT R2) (all R) :- (pi x\ typeOf (R2 x) (R x)).

typeOf (appT E X) (R X) :- typeOf E (all R).

step (appT (absT R2) X) (R2 X).

value (absT R1).


% context appT C e.