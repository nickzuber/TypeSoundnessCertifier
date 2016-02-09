sig stlc_par_unitt.

kind typ, term type.

type arrow typ -> typ -> typ.
type unitType typ.
type abs (term -> term) -> typ -> term.
type unit term.
type app term -> term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
