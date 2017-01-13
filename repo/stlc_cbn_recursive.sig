sig stlc_par.

kind term type.
kind typ type.

type arrow typ -> typ -> typ.
type abs typ -> (term -> term) -> term.
type app term -> term -> term.
type mu (typ -> typ) -> typ.
type fold term -> (typ -> typ) -> term.
type unfold term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.