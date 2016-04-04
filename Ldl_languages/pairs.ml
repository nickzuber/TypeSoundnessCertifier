
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let times_decl = DeclType("times", [Simple("typ") ; Simple("typ")])
let pair_decl valpos ctx = DeclTrm("pair", valpos, ctx, [Simple("term"); Simple("term")])
let fst_decl valpos ctx = DeclTrm("fst", valpos, ctx, [Simple("term")])
let snd_decl valpos ctx = DeclTrm("snd", valpos, ctx, [Simple("term")])


let pair = 
Rule("pair",
				[Formula("typeOf", [Var("E1")] ,  [Var("T1")]) ; Formula("typeOf", [Var("E2")] ,  [Var("T2")]) ],
	
				Formula("typeOf", [Constructor( "pair", [Var("E1") ; Var("E2")])], [Constructor( "times", [Var("T1") ; Var("T2")])])) 

let fstt = 
Rule("fst",
		 		[Formula("typeOf", [Var("E")], [Constructor( "times", [Var("T1") ; Var("T2")])])],
	
				Formula("typeOf", [Constructor( "fst", [Var("E")])], [Var("T1")])) 

let sndd = 
Rule("snd",
 				[Formula("typeOf", [Var("E")], [Constructor( "times", [Var("T1") ; Var("T2")])])],
 
 			   	Formula("typeOf", [Constructor( "snd", [Var("E")])], [Var("T2")])) 


let fstStep = [Rule("fstStep",
	[],
	Formula("step",
		[Constructor( "fst", [Constructor( "pair", [Var("E1") ; Var("E2")])])],
		[Var("E1")]  )  ) 
		]
let sndStep = [Rule("sndStep",
	[],
	Formula("step",
		[Constructor( "snd", [Constructor( "pair", [Var("E1") ; Var("E2")])])],
		[Var("E2")]  )  ) 				
		]
		
let pair_ts v1 c1 v2 c2 v3 c3 = [SpecType(times_decl, 
				[SpecTerm(pair_decl v1 c1, pair, [])], 
				[SpecTerm(fst_decl v2 c2, fstt, fstStep) ;
				 SpecTerm(snd_decl v3 c3, sndd, sndStep) 
				])]

let pairs v1 c1 v2 c2 v3 c3 = SafeTypedLanguage(pair_ts v1 c1 v2 c2 v3 c3, [], None)

let pairs_lazy = pairs        [] [(1,[]) ; (2,[])]       [1] [(1,[])]         [1] [(1,[])]
let pairs_superlazy = pairs        [] []       [1] [(1,[])]         [1] [(1,[])]
let pairs_plain = pairs        [1 ; 2] [(1,[]) ; (2,[])]       [1] [(1,[])]         [1] [(1,[])]
let pairs_onlyfstButBoth = pairs        [1] [(1,[]) ; (2,[])]       [1] [(1,[])]         [1] [(1,[])]
let pairs_onlysnd = pairs        [2] [(2,[])]       [1] [(1,[])]         [1] [(1,[])]

let stlc_cbn_pairs_lazy = sl_compose stlc_cbn pairs_lazy
let stlc_cbn_pairs_superlazy = sl_compose stlc_cbn pairs_superlazy
let stlc_cbn_pairs_plain = sl_compose stlc_cbn pairs_plain
let stlc_cbn_pairs_onlyfstButBoth = sl_compose stlc_cbn pairs_onlyfstButBoth
let stlc_cbn_pairs_onlysnd = sl_compose stlc_cbn pairs_onlysnd

let stlc_cbv_pairs_lazy = sl_compose stlc_cbv pairs_lazy
let stlc_cbv_pairs_superlazy = sl_compose stlc_cbv pairs_superlazy
let stlc_cbv_pairs_plain = sl_compose stlc_cbv pairs_plain
let stlc_cbv_pairs_onlyfstButBoth = sl_compose stlc_cbv pairs_onlyfstButBoth
let stlc_cbv_pairs_onlysnd = sl_compose stlc_cbv pairs_onlysnd

let stlc_par_pairs_lazy = sl_compose stlc_par pairs_lazy
let stlc_par_pairs_superlazy = sl_compose stlc_par pairs_superlazy
let stlc_par_pairs_plain = sl_compose stlc_par pairs_plain
let stlc_par_pairs_onlyfstButBoth = sl_compose stlc_par pairs_onlyfstButBoth
let stlc_par_pairs_onlysnd = sl_compose stlc_par pairs_onlysnd


