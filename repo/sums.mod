module sums.

typeOf (inl E) (sum T1 T2) :- typeOf E T1.

typeOf (inr E) (sum T1 T2) :- typeOf E T2.

typeOf (case EE R1 R2) T :- typeOf EE (sum T1 T2), (pi x\ typeOf x T1 => typeOf (R1 x) T), (pi x\ typeOf x T2 => typeOf (R2 x) T).

step (case (inl EE) R1 R2) (R1 EE).

step (case (inr EE) R1 R2) (R2 EE).

value (inl E1) :- value E1.

value (inr E1) :- value E1.

% context inl E.
% context inr E.
% context case E e e.
