sig systemF.

kind typ, term type.

type arrow typ -> typ -> typ.
type all (typ -> typ) -> typ.
type abs (term -> term) -> typ -> term.
type absT (typ -> term) -> term.
type app term -> term -> term.
type appT term -> typ -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
