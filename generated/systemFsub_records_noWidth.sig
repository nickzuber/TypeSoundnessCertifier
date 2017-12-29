sig systemFsub_records_noWidth.

kind term type.
kind typ type.

kind label type.kind list_record type.
kind list_Trecord type.

type empty_record list_record.
type cons_record label -> term -> list_record -> list_record.
type emptyT_record list_Trecord.
type consT_record label -> typ -> list_Trecord -> list_Trecord.

type record_member list_record -> label -> term -> o.
type recordT_member list_Trecord -> label -> typ -> o.
type record_update list_record -> label -> term -> list_record -> o.
type recordT list_Trecord -> typ.
type arrow typ -> typ -> typ.
type all typ -> (typ -> typ) -> typ.
type top typ.
type record list_record -> term.

type abs typ -> (term -> term) -> term.
type absT typ -> (typ -> term) -> term.
type topObj term.
type projection term -> label -> term.
type app term -> term -> term.
type appT term -> typ -> term.

type value term -> o.

type error term -> o.


type typeOf term -> typ -> o.

type step term -> term -> o.

type nstep term -> term -> o.
type subtype typ -> typ -> o.
