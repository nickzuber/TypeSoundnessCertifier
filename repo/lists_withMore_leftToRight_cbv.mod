module stlc_cbn_sums.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (inl E) (sum T1 T2) :- typeOf E T1.

typeOf (inr E) (sum T1 T2) :- typeOf E T2.

typeOf (emptyList ) (list T).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T R) E) (R E) :- value E.

typeOf (case EE R1 R2) T :- typeOf EE (sum T1 T2), (pi x\ typeOf x T1 => typeOf (R1 x) T), (pi x\ typeOf x T2 => typeOf (R2 x) T).

step (case (inl V) R1 R2) (R1 V) :- value V.

step (case (inr V) R1 R2) (R2 V) :- value V.

typeOf (head E) T :- typeOf E (list T).

step (head (emptyList )) (myError ).

step (head (cons E1 E2)) E1.

typeOf (tail E) (list T) :- typeOf E (list T).

step (tail (emptyList )) (myError ).

step (tail (cons E1 E2)) E2.

value (emptyList ).

value (cons E1 E2) :- value E1, value E2.

value (abs T1 R2).

value (inl E1) :- value E1.

value (inr E1) :- value E1.

error (myError ).

typeOf (myError ) T.

% context inl C.
% context inr C.
% context app C e.
% context app v C.
% context case C e e.
% context cons C v.
% context cons e C.
% context head C.
% context tail C.
