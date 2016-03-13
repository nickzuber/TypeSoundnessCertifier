sig sums.

kind typ, term type.

type sum typ -> typ -> typ.
type inl term -> term.
type inr term -> term.
type case term -> (term -> term) -> (term -> term) -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
