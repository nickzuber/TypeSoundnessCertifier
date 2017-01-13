sig fpl_cbv.

kind term type.
kind typ type.

type mu (typ -> typ) -> typ.
type all (typ -> typ) -> typ.
type list typ -> typ.
type sum typ -> typ -> typ.
type times typ -> typ -> typ.
type bool typ.
type int typ.
type arrow typ -> typ -> typ.
type fold term -> (typ -> typ) -> term.
type absT (typ -> term) -> term.
type cons term -> term -> term.
type emptyList term.
type inr term -> term.
type inl term -> term.
type pair term -> term -> term.
type ff term.
type tt term.
type succ term -> term.
type zero term.
type abs typ -> (term -> term) -> term.
type unfold term -> term.
type appT term -> typ -> term.
type tail term -> term.
type head term -> term.
type case term -> (term -> term) -> (term -> term) -> term.
type snd term -> term.
type fst term -> term.
type if term -> term -> term -> term.
type pred term -> term.
type app term -> term -> term.
type letrec typ -> (term -> term) -> (term -> term) -> term.
type fix term -> term.
type try term -> term -> term.
type raise term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
