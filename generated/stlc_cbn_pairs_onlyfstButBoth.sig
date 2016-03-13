sig stlc_cbn_pairs_onlyfstButBoth.

kind typ, term type.

type arrow typ -> typ -> typ.
type times typ -> typ -> typ.
type abs (term -> term) -> typ -> term.
type pair term -> term -> term.
type app term -> term -> term.
type fst term -> term.
type snd term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
