sig stlc_cbn_lists_lazy.

kind term type.
kind typ type.

type list typ -> typ.
type arrow typ -> typ -> typ.
type cons term -> term -> term.
type emptyList term.
type abs (term -> term) -> typ -> term.
type tail term -> term.
type head term -> term.
type app term -> term -> term.
type myError term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
