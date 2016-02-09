

open TypedLanguage
open SafeTypedLanguage
open Stlc
open Iff
open ListsWithExc
open Letrec
open Exception
open Forall

let fullFledged_cbn = sl_compose (sl_compose (sl_compose stlc_cbn_letrec forall) listsWithExc) iff 
let fullFledged_cbv = sl_compose (sl_compose (sl_compose stlc_cbv_letrec forall) listsWithExc) iff
let fullFledged_par = sl_compose (sl_compose (sl_compose stlc_par_letrec forall) listsWithExc) iff 
