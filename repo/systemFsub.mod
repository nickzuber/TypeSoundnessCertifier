module systemFsub.

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (absT T1 R2) (all T1 R) :- (pi x\ subtype x T1 => typeOf (R2 x) (R x)).

typeOf (topObj) (top).

typeOf (app E1 E2) T2 :- typeOf E1 (arrow T1' T2), typeOf E2 T1'.

step (app (abs T1 R) V) (R V) :- value V.

typeOf (appT E X) (R' X) :- typeOf E (all T2 R'), subtype X T2.

step (appT (absT T1 R2) X) (R2 X).

value (abs T1 R2).

value (absT T R1).

% context app C e.
% context app v C.
% context appT C e.
% declarative-subtyping.
% subtyping-top top.
% contravariant arrow 1.
% subtyping-for all: subtype (all T1 T2) (all T1' T2') :- subtype T1' T1, (pi x\ subtype x T1' => subtype (T2 x) (T2' x)).



