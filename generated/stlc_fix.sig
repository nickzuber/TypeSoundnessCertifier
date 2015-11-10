sig stlc_fix.

kind typ, term type.

type arrow typ -> typ -> typ.
type abs (term -> term) -> typ -> term.
type app term -> term -> term.
type fix term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
