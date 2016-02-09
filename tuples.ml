
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let times5_decl = DeclType("times5", [Simple("typ") ; Simple("typ") ; Simple("typ") ; Simple("typ") ; Simple("typ")])
let tuples5_decl valpos ctx = DeclTrm("tuple5", valpos, ctx, [Simple("term") ; Simple("term") ; Simple("term") ; Simple("term") ; Simple("term")])
let select1_decl = DeclTrm("select1", [1], [(1,[])], [Simple("term")])
let select2_decl = DeclTrm("select2", [1], [(1,[])], [Simple("term")])
let select3_decl = DeclTrm("select3", [1], [(1,[])], [Simple("term")])
let select4_decl = DeclTrm("select4", [1], [(1,[])], [Simple("term")])
let select5_decl = DeclTrm("select5", [1], [(1,[])], [Simple("term")])


let tuple5 = 
Rule("tuple5",
				[Formula("typeOf", [Var("E1")] ,  [Var("T1")]) ; 
				Formula("typeOf", [Var("E2")] ,  [Var("T2")]) ;
				Formula("typeOf", [Var("E3")] ,  [Var("T3")]) ;
				Formula("typeOf", [Var("E4")] ,  [Var("T4")]) ;
				Formula("typeOf", [Var("E5")] ,  [Var("T5")]) ],

				Formula("typeOf", [Constructor( "tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])) 

let select1 = 
Rule("select1",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select1", [Var("E")])], [Var("T1")])) 

let select2 = 
Rule("select2",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select2", [Var("E")])], [Var("T2")])) 

let select3 = 
Rule("select3",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select3", [Var("E")])], [Var("T3")])) 

let select4 = 
Rule("select4",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select4", [Var("E")])], [Var("T4")])) 

let select5 = 
Rule("select5",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select5", [Var("E")])], [Var("T5")])) 


let select1Semantics = [Rule("select1Step", 
						[],
						Formula("step", [Constructor( "select1", [Constructor("tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])], [Var("E1")]))
						]
let select2Semantics = [Rule("select2Step", 
						[],
						Formula("step", [Constructor( "select2", [Constructor("tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])], [Var("E2")]))
						]
let select3Semantics = [Rule("select3Step", 
						[],
						Formula("step", [Constructor( "select3", [Constructor("tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])], [Var("E3")]))
						]
let select4Semantics = [Rule("select4Step", 
						[],
						Formula("step", [Constructor( "select4", [Constructor("tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])], [Var("E4")]))
						]
let select5Semantics = [Rule("select5Step", 
						[],
						Formula("step", [Constructor( "select5", [Constructor("tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])], [Var("E5")]))
						]

let tuples_ts v c = [SpecType(times5_decl, 
				[SpecTerm(tuples5_decl v c, tuple5, [])], 
				[
				SpecTerm(select1_decl, select1, select1Semantics) ;
				SpecTerm(select2_decl, select2, select2Semantics) ;
				SpecTerm(select3_decl, select3, select3Semantics) ;
				SpecTerm(select4_decl, select4, select4Semantics) ;
				SpecTerm(select5_decl, select5, select5Semantics) 
				])]

let tuples_ v c = SafeTypedLanguage(tuples_ts v c, [], None)

let tuples_lazy = tuples_ [] []
let tuples_parallel = tuples_ [1 ; 2 ; 3 ; 4 ; 5] [(1,[]) ; (2,[]) ; (3,[]) ; (4,[]) ; (5,[])]   
let tuples_plain = tuples_ [1 ; 2 ; 3 ; 4 ; 5] [(1,[]) ; (2,[1]) ; (3,[1;2]) ; (4,[1;2;3]) ; (5,[1;2;3;4])]   

let stlc_cbn_tuples_lazy = sl_compose stlc_cbn tuples_lazy
let stlc_cbn_tuples_parallel = sl_compose stlc_cbn tuples_parallel
let stlc_cbn_tuples_plain = sl_compose stlc_cbn tuples_plain

let stlc_cbv_tuples_lazy = sl_compose stlc_cbv tuples_lazy
let stlc_cbv_tuples_parallel = sl_compose stlc_cbv tuples_parallel
let stlc_cbv_tuples_plain = sl_compose stlc_cbv tuples_plain

let stlc_par_tuples_lazy = sl_compose stlc_par tuples_lazy
let stlc_par_tuples_parallel = sl_compose stlc_par tuples_parallel
let stlc_par_tuples_plain = sl_compose stlc_par tuples_plain



