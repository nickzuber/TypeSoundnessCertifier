module lists_rightToleft.

typeOf (emptyList ) (list T).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (head E) T :- typeOf E (list T).

step (head (emptyList )) (myError ).

step (head (cons E1 E2)) E1.

typeOf (tail E) (list T) :- typeOf E (list T).

step (tail (emptyList )) (myError ).

step (tail (cons E1 E2)) E2.

value (emptyList ).

value (cons E1 E2) :- value E1, value E2.

error (myError ).

typeOf (myError ) T.


% context cons E v.
% context cons e E.
% context head E.
% context tail E.
