sig stlc_cbn_iff_par.

kind term type.
kind typ type.

type bool typ.
type arrow typ -> typ -> typ.
type ff term.
type tt term.
type abs typ -> (term -> term) -> term.
type if term -> term -> term -> term.
type app term -> term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
