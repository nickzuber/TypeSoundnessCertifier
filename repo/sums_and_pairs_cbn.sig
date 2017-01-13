sig stlc_cbv_sums.

kind term type.
kind typ type.

type arrow typ -> typ -> typ.
type sum typ -> typ -> typ.
type abs typ -> (term -> term) -> term.
type inl term -> term.
type inr term -> term.
type app term -> term -> term.
type case term -> (term -> term) -> (term -> term) -> term.
type times typ -> typ -> typ.
type pair term -> term -> term.
type fst term -> term.
type snd term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
