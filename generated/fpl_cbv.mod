module fpl_cbv.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (succ E) (int ) :- typeOf E (int ).

typeOf (zero ) (int ).

typeOf (ff ) (bool ).

typeOf (tt ) (bool ).

typeOf (pair E1 E2) (times T1 T2) :- typeOf E1 T1, typeOf E2 T2.

typeOf (inr E) (sum T1 T2) :- typeOf E T2.

typeOf (inl E) (sum T1 T2) :- typeOf E T1.

typeOf (cons E1 E2) (list T) :- typeOf E1 T, typeOf E2 (list T).

typeOf (emptyList ) (list T).

typeOf (absT R2) (all R) :- (pi x\ typeOf (R2 x) (R x)).

typeOf (fold E R) (mu R) :- typeOf E (R (mu R)).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1 T2), typeOf E2 T1.

step (app (abs T1 R) V) (R V) :- value V.

typeOf (pred E') (int ) :- typeOf E' (int ).

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

step (case (inl E) R1 R2) (R1 E) :- value E.

step (case (inr E) R1 R2) (R2 E) :- value E.

typeOf (head E) T :- typeOf E (list T).

step (head (emptyList )) (raise (zero )).

step (head (cons E1 E2)) E1.

typeOf (tail E) (list T) :- typeOf E (list T).

step (tail (emptyList )) (raise (succ (zero ))).

step (tail (cons E1 E2)) E2.

typeOf (appT E X) (R X) :- typeOf E (all R).

step (appT (absT R2) X) (R2 X).

typeOf (unfold E') (R (mu R)) :- typeOf E' (mu R).

step (unfold (fold E R)) E :- value E.

typeOf (letrec T1 R1 R2) T2 :- (pi x\ typeOf x T1 => typeOf (R1 x) T1), (pi x\ typeOf x T1 => typeOf (R2 x) T2).

step (letrec T1 R1 R2) (R2 (fix (abs T1 R1))).

typeOf (fix E) T :- typeOf E (arrow T T).

step (fix E) (app E (fix E)) :- value E.

typeOf (try E1' E2) T :- typeOf E1' T, typeOf E2 (arrow (int ) T).

step (try E1 E2) E1 :- value E1.

step (try (raise E1) E2) (app E2 E1).

value (abs T1 R2).

value (succ E1) :- value E1.

value (zero ).

value (ff ).

value (tt ).

value (pair E1 E2) :- value E1, value E2.

value (inr E1) :- value E1.

value (inl E1) :- value E1.

value (cons E1 E2) :- value E1, value E2.

value (emptyList ).

value (absT R1).

value (fold E1 U2) :- value E1.

step (succ E1) (succ E1') :- step E1 E1'.

step (pair E1 E2) (pair E1' E2) :- step E1 E1'.

step (pair E1 E2) (pair E1 E2') :- step E2 E2', value E1.

step (inr E1) (inr E1') :- step E1 E1'.

step (inl E1) (inl E1') :- step E1 E1'.

step (cons E1 E2) (cons E1' E2) :- step E1 E1'.

step (cons E1 E2) (cons E1 E2') :- step E2 E2', value E1.

step (fold E1 U2) (fold E1' U2) :- step E1 E1'.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2', value E1.

step (pred E1) (pred E1') :- step E1 E1'.

step (if E1 E2 E3) (if E1' E2 E3) :- step E1 E1'.

step (fst E1) (fst E1') :- step E1 E1'.

step (snd E1) (snd E1') :- step E1 E1'.

step (case E1 R2 R3) (case E1' R2 R3) :- step E1 E1'.

step (head E1) (head E1') :- step E1 E1'.

step (tail E1) (tail E1') :- step E1 E1'.

step (appT E1 T2) (appT E1' T2) :- step E1 E1'.

step (unfold E1) (unfold E1') :- step E1 E1'.

step (fix E1) (fix E1') :- step E1 E1'.

step (try E1 E2) (try E1' E2) :- step E1 E1'.

step (raise E1) (raise E1') :- step E1 E1'.

error (raise E1).

typeOf (raise E1) T :- typeOf E1 (int ).

step (succ E1) E1 :- error E1.

step (pair E1 E2) E1 :- error E1.

step (pair E1 E2) E2 :- error E2.

step (inr E1) E1 :- error E1.

step (inl E1) E1 :- error E1.

step (cons E1 E2) E1 :- error E1.

step (cons E1 E2) E2 :- error E2.

step (fold E1 U2) E1 :- error E1.

step (app E1 E2) E1 :- error E1.

step (app E1 E2) E2 :- error E2.

step (pred E1) E1 :- error E1.

step (if E1 E2 E3) E1 :- error E1.

step (fst E1) E1 :- error E1.

step (snd E1) E1 :- error E1.

step (case E1 R2 R3) E1 :- error E1.

step (head E1) E1 :- error E1.

step (tail E1) E1 :- error E1.

step (appT E1 T2) E1 :- error E1.

step (unfold E1) E1 :- error E1.

step (fix E1) E1 :- error E1.

step (raise E1) E1 :- error E1.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.

