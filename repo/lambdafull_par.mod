module lambdafull_par.

typeOf (abs R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (fold E R) (mu R) :- typeOf E (R (mu R)).

typeOf (emptyList ) (list T).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (excValue ) (excType ).

typeOf (tt ) (bool ).

typeOf (ff ) (bool ).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs R) EE) (R EE).

typeOf (unfold E) (R (mu R)) :- typeOf E (mu R).

step (unfold (fold V R)) V :- value V.

typeOf (head E) T :- typeOf E (list T).

step (head (emptyList )) (raise (excValue )).

step (head (cons E1 E2)) E1.

typeOf (tail E) (list T) :- typeOf E (list T).

step (tail (emptyList )) (raise (excValue )).

step (tail (cons E1 E2)) E2.

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

typeOf (fix E) T :- typeOf E (arrow T T).

step (fix V) (app V (fix V)) :- value V.

typeOf (letrec R1 R2) T2 :- (pi x\ typeOf x T1 => typeOf (R1 x) T1), (pi x\ typeOf x T1 => typeOf (R2 x) T2).

step (letrec R1 R2) (R2 (fix (abs R1))).

typeOf (try E1 E2) T :- typeOf E1 T, typeOf E2 (arrow (excType ) T).

step (try E1 E2) E1 :- value E1.

step (try (raise E1) E2) (app E2 E1).

value (abs R1).

value (fold E1 U2) :- value E1.

value (emptyList ).

value (cons E1 E2) :- value E1, value E2.

value (excValue ).

value (tt ).

value (ff ).

error (raise E1) :- value E1.

typeOf (raise E) T :- typeOf E (excType ).


% context fold C e.

% context cons C e.
% context cons v C.



% context app C e.
% context app e C.
% context unfold C.
% context head C.
% context tail C.
% context if C e e.
% context fix C.

% context try C e.
% context raise C.