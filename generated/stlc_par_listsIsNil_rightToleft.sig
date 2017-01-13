sig stlc_par_listsIsNil_rightToleft.

kind term type.
kind typ type.

type bool typ.
type list typ -> typ.
type arrow typ -> typ -> typ.
type ff term.
type tt term.
type cons term -> term -> term.
type emptyList term.
type abs typ -> (term -> term) -> term.
type if term -> term -> term -> term.
type isnil term -> term.
type tail term -> term.
type head term -> term.
type app term -> term -> term.
type myError term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
