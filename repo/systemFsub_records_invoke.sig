sig systemFsub_records.

kind term type.
kind typ type.

type top typ.
type arrow typ -> typ -> typ.
type all typ -> (typ -> typ) -> typ.
type abs typ -> (term -> term) -> term.
type absT typ -> (typ -> term) -> term.
type app term -> term -> term.
type appT term -> typ -> term.
type topObj term.

type record (record-list T) -> term.
type projection term -> label -> term.
type invoke term -> label -> term -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type subtype typ -> typ -> o.
