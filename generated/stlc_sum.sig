sig stlc_sum.

kind typ, term type.

type arrow typ -> typ -> typ.
type sum typ -> typ -> typ.
type abs (term -> term) -> typ -> term.
type inl term -> term.
type inr term -> term.
type app term -> term -> term.
type case term -> (term -> term) -> (term -> term) -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
