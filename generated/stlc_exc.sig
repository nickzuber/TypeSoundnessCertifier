sig stlc_exc.

kind typ, term type.

type arrow typ -> typ -> typ.
type excType typ.
type abs (term -> term) -> term.
type excValue term.
type app term -> term -> term.
type try term -> term -> term.
type raise term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
