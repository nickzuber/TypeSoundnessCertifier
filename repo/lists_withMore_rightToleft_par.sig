sig lists_withMore_rightToleft_par.

kind term type.
kind typ type.

type arrow typ -> typ -> typ.
type sum typ -> typ -> typ.
type abs typ -> (term -> term) -> term.
type inl term -> term.
type inr term -> term.
type app term -> term -> term.
type case term -> (term -> term) -> (term -> term) -> term.
type list typ -> typ.
type emptyList term.
type cons term -> term -> term.
type head term -> term.
type tail term -> term.
type myError term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
