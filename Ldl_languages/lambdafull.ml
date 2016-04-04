

open TypedLanguage
open SafeTypedLanguage
open Stlc
open Itlc
open Iff
open ListsWithExc
open LetrecFix
open Exception
open Forall
open Recursive

let lambdafull_cbn = sl_compose (sl_compose (sl_compose itlc_cbn_letrecFix recursive) listsWithExc) iff 
let lambdafull_cbv = sl_compose (sl_compose (sl_compose itlc_cbn_letrecFix recursive) listsWithExc) iff
let lambdafull_par = sl_compose (sl_compose (sl_compose itlc_cbn_letrecFix recursive) listsWithExc) iff 
