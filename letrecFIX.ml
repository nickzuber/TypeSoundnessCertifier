
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc
open Fix
open Letrec

let letrecFixSemantics = 
		[
		Rule("letrecStep",
			[],
			Formula("step",
				[Constructor( "letrec", [Var("R1") ; Var("R2")])],
				[Application(Var("R2"), Constructor( "fix", [Constructor( "abs", [Var("R1")])]))]
			))]
				
let letrecFix_ts = [SpecTerm(letrec_decl, letrecc, letrecFixSemantics)]

let letrecFix = SafeTypedLanguage([], letrecFix_ts, None)
let itlc_cbn_letrecFix = sl_compose itlc_cbn_fix letrecFix
let itlc_cbv_letrecFix = sl_compose itlc_cbv_fix letrecFix
let itlc_par_letrecFix = sl_compose itlc_par_fix letrecFix

