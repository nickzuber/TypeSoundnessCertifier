module systemFsub_records_invariant.

typeOf (record (empty_record )) (recordT (emptyT_record )).

typeOf (record (cons_record L E Rest1)) (recordT (consT_record L T Rest2)) :- typeOf E T, typeOf (record Rest1) (recordT Rest2).

typeOf (abs T1 R) (arrow T1 T2) :- (pi x\ typeOf x T1 => typeOf (R x) T2).

typeOf (absT T1 R2) (all T1 R) :- (pi x\ subtype x T1 => typeOf (R2 x) (R x)).

typeOf (topObj ) (top ).

typeOf (projection E' L') T :- typeOf E' (recordT List), recordT_member List L' T.

step (projection (record ListExp) L) E' :- record_member ListExp L E'.

typeOf (app E1 E2) T2' :- typeOf E1 (arrow T1' T2'), typeOf E2 T1'.

step (app (abs T1 R) V) (R V) :- value V.

typeOf (appT E X) (R' X) :- typeOf E (all T2 R'), subtype X T2.

step (appT (absT T1 R2) X) (R2 X).

value (record (empty_record )).

value (record (cons_record L V Rest)).

value (abs T1 R2).

value (absT T1 R2).

value (topObj ).

step (record (cons_record L E Rest)) (record (cons_record L E' Rest)) :- step E E'.

step (record (cons_record L E Rest)) (record (cons_record L E Rest')) :- step (record Rest) (record Rest'), value E.

step (projection E1 L) (projection E1' L) :- step E1 E1'.

step (app E1 E2) (app E1' E2) :- step E1 E1'.

step (app E1 E2) (app E1 E2') :- step E2 E2', value E1.

step (appT E1 T2) (appT E1' T2) :- step E1 E1'.

nstep E E.

nstep E1 E3 :- step E1 E2, nstep E2 E3.

record_member (cons_record L T Rest) L T.

record_member (cons_record L1 T1 Rest) L T :- record_member Rest L T.

recordT_member (consT_record L E Rest) L E.

recordT_member (consT_record L1 E1 Rest) L E :- recordT_member Rest L E.

record_update (cons_record L E1 Rest) L E2 (cons_record L E2 Rest).

record_update (cons_record L1 E1 Rest) L2 E2 (cons_record L1 E1 Rest2) :- record_update Rest L2 E2 Rest2.

subtype T (top ).

subtype (arrow T1 T2) (arrow T1' T2') :- subtype T1' T1, subtype T2 T2'.

subtype (recordT (consT_record L T1 Rest1)) (recordT (consT_record L T1 Rest1')) :- subtype (recordT Rest1) (recordT Rest1').

subtype (recordT (emptyT_record )) (recordT (emptyT_record )).

subtype (recordT (consT_record L T Rest)) (recordT (emptyT_record )).

subtype (all T1 T2) (all T1' T2') :- subtype T1' T1, (pi x\ subtype x T1' => subtype (T2 x) (T2' x)).

subtype T T.

subtype T1 T3 :- subtype T1 T2, subtype T2 T3.

typeOf E T :- typeOf E S, subtype S T.
