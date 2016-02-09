sig itlc_par_letrec.

kind typ, term type.

type arrow typ -> typ -> typ.
type abs (term -> term) -> term.
type app term -> term -> term.
type fix term -> term.
type let term -> (term -> term) -> term.
type letrec (term -> term) -> (term -> term) -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
