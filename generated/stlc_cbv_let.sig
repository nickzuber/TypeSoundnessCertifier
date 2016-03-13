sig stlc_cbv_let.

kind typ, term type.

type arrow typ -> typ -> typ.
type abs (term -> term) -> typ -> term.
type app term -> term -> term.
type let term -> (term -> term) -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
