

open TypedLanguage
open SafeTypedLanguage
open Stlc
open Itlc
open Iff
open ListsWithExc
open Letrec
open LetrecWithType
open Exception
open Forall

let fullFledged_cbn = sl_compose (sl_compose (sl_compose itlc_cbn_letrec forall) listsWithExc) iff 
let fullFledged_cbv = sl_compose (sl_compose (sl_compose itlc_cbv_letrec forall) listsWithExc) iff
let fullFledged_par = sl_compose (sl_compose (sl_compose itlc_par_letrec forall) listsWithExc) iff 
