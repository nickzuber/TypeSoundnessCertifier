module recursive.

typeOf (fold E R) (mu R) :- typeOf E (R (mu R)).

typeOf (unfold E) (R (mu R)) :- typeOf E (mu R).

step (unfold (fold V R)) V :- value V.

value (fold E1 U2) :- value E1.

% context fold C e.
% context unfold C.