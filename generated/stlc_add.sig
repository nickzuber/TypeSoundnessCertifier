sig stlc_add.

kind typ, term type.

type arrow typ -> typ -> typ.
type int typ.
type abs (term -> term) -> typ -> term.
type zero term.
type succ term -> term.
type app term -> term -> term.
type add term -> term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
