sig mycalculus.

kind typ, term type.

type arrow typ -> typ -> typ.
type bool typ.
type times typ -> typ -> typ.
type abs (term -> term) -> term.
type tt term.
type ff term.
type pair term -> term -> term.
type app term -> term -> term.
type if term -> term -> term -> term.
type fst term -> term.
type snd term -> term.

type termPred term  -> o.

type value term -> o.

type nonvalue term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.
