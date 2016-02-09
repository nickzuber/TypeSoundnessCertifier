

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

let fullFledgedWithType_cbn = sl_compose (sl_compose (sl_compose stlc_cbn_letrecWithType forall) listsWithExc) iff 
let fullFledgedWithType_cbv = sl_compose (sl_compose (sl_compose stlc_cbv_letrecWithType forall) listsWithExc) iff
let fullFledgedWithType_par = sl_compose (sl_compose (sl_compose stlc_par_letrecWithType forall) listsWithExc) iff 
