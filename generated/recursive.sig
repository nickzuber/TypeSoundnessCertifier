sig recursive.

kind typ, term type.

type mu (typ -> typ) -> typ.
type fold term -> (typ -> typ) -> term.
type unfold term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
