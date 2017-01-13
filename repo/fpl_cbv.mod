module fpl_cbv.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (zero ) (int ).

typeOf (succ E) (int ) :- typeOf E (int ).

typeOf (tt ) (bool ).

typeOf (ff ) (bool ).

typeOf (pair E1 E2) (times T1 T2) :- typeOf E1 T1, typeOf E2 T2.

typeOf (inl E) (sum T1 T2) :- typeOf E T1.

typeOf (inr E) (sum T1 T2) :- typeOf E T2.

typeOf (emptyList ) (list T).

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (absT R2) (all R) :- (pi x\ typeOf (R2 x) (R x)).

typeOf (fold E R) (mu R) :- typeOf E (R (mu R)).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T R) V) (R V) :- value V.

typeOf (pred E) (int ) :- typeOf E (int ).

step (pred (zero )) (raise (zero )).

step (pred (succ E)) E.

typeOf (if E1 E2 E3) T :- typeOf E1 (bool ), typeOf E2 T, typeOf E3 T.

step (if (tt ) E1 E2) E1.

step (if (ff ) E1 E2) E2.

typeOf (fst E) T1 :- typeOf E (times T1 T2).

step (fst (pair E1 E2)) E1.

typeOf (snd E) T2 :- typeOf E (times T1 T2).

step (snd (pair E1 E2)) E2.

typeOf (case EE R1 R2) T :- typeOf EE (sum T1 T2), (pi x\ typeOf x T1 => typeOf (R1 x) T), (pi x\ typeOf x T2 => typeOf (R2 x) T).

step (case (inl EE) R1 R2) (R1 EE).

step (case (inr EE) R1 R2) (R2 EE).

typeOf (head E) T :- typeOf E (list T).

step (head (emptyList )) (raise (zero )).

step (head (cons E1 E2)) E1.

typeOf (tail E) (list T) :- typeOf E (list T).

step (tail (emptyList )) (raise (succ (zero ))).

step (tail (cons E1 E2)) E2.

typeOf (appT E X) (R X) :- typeOf E (all R).

step (appT (absT R2) X) (R2 X).

typeOf (unfold E) (R (mu R)) :- typeOf E (mu R).

step (unfold (fold V R)) V :- value V.

typeOf (fix E) T :- typeOf E (arrow T T).

step (fix V) (app V (fix V)) :- value V.

typeOf (letrec T1 R1 R2) T2 :- (pi x\ typeOf x T1 => typeOf (R1 x) T1), (pi x\ typeOf x T1 => typeOf (R2 x) T2).

step (letrec T1 R1 R2) (R2 (fix (abs T1 R1))).

typeOf (try E1 E2) T :- typeOf E1 T, typeOf E2 (arrow (int ) T).

step (try E1 E2) E1 :- value E1.

step (try (raise E1) E2) (app E2 E1).

value (abs T1 R2).

value (zero ).

value (succ E1) :- value E1.

value (tt ).

value (ff ).

value (pair E1 E2) :- value E1, value E2.

value (inl E1) :- value E1.

value (inr E1) :- value E1.

value (emptyList ).

value (cons E1 E2) :- value E1, value E2.

value (absT R1).

value (fold E1 U2) :- value E1.

error (raise E1) :- value E1.

typeOf (raise E) T :- typeOf E (int ).



% context succ E.


% context pair E e.
% context pair v E.
% context inl E.
% context inr E.

% context cons E e.
% context cons v E.

% context fold E e.
% context app E e.
% context app v E.
% context pred E.
% context if E e e.
% context fst E.
% context snd E.
% context case E e e.
% context head E.
% context tail E.
% context appT E e.
% context unfold E.
% context fix E.

% context try E e.
% context raise E.
