sig fullFledged_par.

kind typ, term type.

type arrow typ -> typ -> typ.
type bool typ.
type list typ -> typ.
type all (typ -> typ) -> typ.
type abs (term -> term) -> typ -> term.
type tt term.
type ff term.
type emptyList term.
type cons term -> term -> term.
type absT (typ -> term) -> term.
type app term -> term -> term.
type if term -> term -> term -> term.
type head term -> term.
type tail term -> term.
type isnil term -> term.
type appT term -> typ -> term.
type let term -> (term -> term) -> term.
type myError term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
