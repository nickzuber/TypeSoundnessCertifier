module stlc_add.

typeOf (abs R T1) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (zero ) (int ).

typeOf (succ E) (int ) :- typeOf E (int ).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

typeOf (add E1 E2) (int ) :- typeOf E1 (int ), typeOf E2 (int ).

step (app (abs R T) EE) (R EE).

step (add (zero ) E) E.

step (add (succ E1) E2) (succ E1).

value (abs R1 T2).

value (zero ).

value (succ E1) :- value E1.

step (succ E1) (succ E1') :- step E1 E1'.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (add E1 E2) (add E1' E2) :- step E1 E1'.

step (add E1 E2) (add E1 E2') :- step E2 E2', value E1.
