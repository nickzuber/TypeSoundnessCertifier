sig stlc_cbn_pairs_lazy.

kind term type.
kind typ type.

type times typ -> typ -> typ.
type arrow typ -> typ -> typ.
type pair term -> term -> term.
type abs (term -> term) -> typ -> term.
type snd term -> term.
type fst term -> term.
type app term -> term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
