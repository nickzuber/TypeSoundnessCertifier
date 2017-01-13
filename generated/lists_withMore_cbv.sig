sig lists_withMore_cbv.

kind term type.
kind typ type.

type list typ -> typ.
type sum typ -> typ -> typ.
type arrow typ -> typ -> typ.
type cons term -> term -> term.
type emptyList term.
type inr term -> term.
type inl term -> term.
type abs typ -> (term -> term) -> term.
type tail term -> term.
type head term -> term.
type case term -> (term -> term) -> (term -> term) -> term.
type app term -> term -> term.
type myError term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
