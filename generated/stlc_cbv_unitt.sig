sig stlc_cbv_unitt.

kind term type.
kind typ type.

kind label type.type arrow typ -> typ -> typ.
type unitType typ.
type abs typ -> (term -> term) -> term.
type unit term.
type app term -> term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
