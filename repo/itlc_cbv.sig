sig itlc_cbv.

kind term type.
kind typ type.

type arrow typ -> typ -> typ.
type abs (term -> term) -> term.
type app term -> term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
