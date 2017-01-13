module listsIsNil_rightToleft.

typeOf (emptyList ) (list T).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (tt ) (bool ).

typeOf (ff ) (bool ).

typeOf (head E) T :- typeOf E (list T).

step (head (emptyList )) (myError ).

step (head (cons E1 E2)) E1.

typeOf (tail E) (list T) :- typeOf E (list T).

step (tail (emptyList )) (myError ).

step (tail (cons E1 E2)) E2.

typeOf (isnil E) (bool ) :- typeOf E (list T).

step (isnil (emptyList )) (tt ).

step (isnil (cons E1 E2)) (ff ).

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

value (emptyList ).

value (cons E1 E2) :- value E1, value E2.

value (tt ).

value (ff ).

error (myError ).

typeOf (myError ) T.


% context cons E v.
% context cons e E.
% context head E.
% context tail E.
% context isnil E.
% context if E e e.
