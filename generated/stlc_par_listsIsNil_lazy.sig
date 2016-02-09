sig stlc_par_listsIsNil_lazy.

kind typ, term type.

type arrow typ -> typ -> typ.
type list typ -> typ.
type bool typ.
type abs (term -> term) -> typ -> term.
type emptyList term.
type cons term -> term -> term.
type tt term.
type ff term.
type app term -> term -> term.
type head term -> term.
type tail term -> term.
type isnil term -> term.
type if term -> term -> term -> term.
type myError term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
