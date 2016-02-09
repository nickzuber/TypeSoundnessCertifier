
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
[Rule("pair",
				[Formula("typeOf", [Var("E1")] ,  [Var("T1")]) ; Formula("typeOf", [Var("E2")] ,  [Var("T2")]) ],
	
				Formula("typeOf", [Constructor( "pair", [Var("E1") ; Var("E2")])], [Constructor( "times", [Var("T1") ; Var("T2")])])) 
]
let fstt = 
[Rule("fst",
		 		[Formula("typeOf", [Var("E")], [Constructor( "times", [Var("T1") ; Var("T2")])])],
	
				Formula("typeOf", [Constructor( "fst", [Var("E")])], [Var("T1")])) 
]
let sndd = 
[Rule("snd",
 				[Formula("typeOf", [Var("E")], [Constructor( "times", [Var("T1") ; Var("T2")])])],
 
 			   	Formula("typeOf", [Constructor( "snd", [Var("E")])], [Var("T2")])) 
]

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
				[SpecTerm(pair_decl v1 c1, pair)], 
				[SpecTerm(fst_decl v2 c2, fstt @ fstStep) ;
				 SpecTerm(snd_decl v3 c3, sndd @ sndStep) 
				],
				None)]

let pairs v1 c1 v2 c2 v3 c3 = SafeTypedLanguage(pair_ts v1 c1 v2 c2 v3 c3, [], None)

let pairs_lazy = pairs        [] [(1,[]) ; (2,[])]       [1] [(1,[])]         [1] [(1,[])]
let pairs_plain = pairs        [1 ; 2] [(1,[]) ; (2,[])]       [1] [(1,[])]         [1] [(1,[])]
let pairs_onlyfst = pairs        [1 ; 2] [(1,[]) ; (2,[])]       [1] [(1,[])]         [1] [(1,[])]
let pairs_onlyfstInfst = pairs        [1 ; 2] [(1,[]) ; (2,[])]       [1] [(1,[])]         [1] [(1,[])]


(*
toContextRulesByCTX (DeclTrm("pair", [], [(1,[]) ; (2,[])], [Simple("term"); Simple("term")])) (2,[]) ;;

(* Declarations Types *)
let excType_decl = [DeclType("excType", [])]
let bool_decl = [DeclType("bool", [])]
let int_decl = [DeclType("int", [])]
let list_decl = [DeclType("list", [Simple("typ")])]

let excValue_decl = [DeclTrm("excValue", Constr "excType", Contextual [], [])]
let fix_decl = [DeclTrm("fix", Derived (Some "arrow"), Contextual [(1,[])], [Simple("term")])]
let true_decl = [DeclTrm("tt", Constr "bool", Contextual [], [])]
let false_decl = [DeclTrm("ff", Constr "bool", Contextual [], [])]
let if_decl = [DeclTrm("if", Destr "bool", Contextual [(1,[]) ; (2,[1]) ; (3,[1 ; 2])], [Simple("term") ; Simple("term") ; Simple("term")])]
let zero_decl = [DeclTrm("zero", Constr "int", Contextual [], [])]
(* at the moment, it only works for values who do not reduce underneath, I should generalize  *)
let succ_decl = [DeclTrm("succ", Constr "int", Contextual [(1,[])], [Simple("term")])]
let isZero_decl = [DeclTrm("isZero", Destr "int", Contextual [(1,[])], [Simple("term")])]
let pred_decl = [DeclTrm("pred", Destr "int", Contextual [(1,[])], [Simple("term")])]
let absInf_decl = [DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")])]
let let_decl = [DeclTrm("let", Derived None, Contextual [(1,[])], [Simple("term") ; Abstraction("term", "term")])]
let letrec_decl = [DeclTrm("letrec", Derived None, Contextual [], [Abstraction("term", "term") ; Abstraction("term", "term")])]
let try_decl = [DeclTrm("try", ErrorHandler, Contextual [(1,[])], [Simple("term"); Simple("term")])]
let raise_decl = [DeclTrm("raise", Error, Contextual [(1,[])], [Simple("term")])]
let emptyList_decl = [DeclTrm("emptyList", Constr "list", Contextual [], [])]
let cons_decl = [DeclTrm("cons", Constr "list", Contextual [], [Simple("term"); Simple("term")])]
let head_decl = [DeclTrm("head", Destr "list", Contextual [(1,[])], [Simple("term")])]
let tail_decl = [DeclTrm("tail", Destr "list", Contextual [(1,[])], [Simple("term")])]
let isnil_decl = [DeclTrm("isnil", Destr "list", Contextual [(1,[])], [Simple("term")])]
let myError_decl = [DeclTrm("myError", Error , Contextual [], [])]
let times_decl = [DeclType("times", [Simple("typ") ; Simple("typ")])]
let pair_decl = [DeclTrm("pair", Constr "times", Contextual [], [Simple("term"); Simple("term")])]
let fst_decl = [DeclTrm("fst", Destr "times", Contextual [(1,[])], [Simple("term")])]
let snd_decl = [DeclTrm("snd", Destr "times", Contextual [(1,[])], [Simple("term")])]
let sum_decl = [DeclType("sum", [Simple("typ") ; Simple("typ")])]
let inl_decl = [DeclTrm("inl", Constr "sum", Contextual [], [Simple("term")])]
let inr_decl = [DeclTrm("inr", Constr "sum", Contextual [], [Simple("term")])]
let case_decl = [DeclTrm("case", Destr "sum", Contextual [(1,[])], [Simple("term"); Abstraction("term", "term") ; Abstraction("term", "term")])]
let unitType_decl = [DeclType("unitType", [])]
let unit_decl = [DeclTrm("unit", Constr "unitType", Contextual [], [])]
let all_decl = [DeclType("all", [Abstraction("typ", "typ")])]
let absT_decl = [DeclTrm("absT", Constr "all", Contextual [], [Abstraction("typ", "term")])]
let appT_decl = [DeclTrm("appT", Destr "all", Contextual [(1,[])], [Simple("term"); Simple("typ")])]

(* Typing rules *)

let abs = 
[Rule("abs",
				[Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
				
	Formula("typeOf",     [Constructor( "abs", [Var("R") ; Var("T1")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])]))
]
let app =
[Rule("app",
				[Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
				 Formula("typeOf", [Var("E2")] ,  [Var("T1")])],
				 
				 Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  )
]
				 			  
let zero = 
[Rule("zero",
				[],
				
				Formula("typeOf", [Constructor( "zero", [])], [Constructor( "int", []) ]  )  ) 		   
]
let succ = 
[Rule("succ",
 				[Formula("typeOf", [Var("E")], [Constructor( "int", []) ])],

				Formula("typeOf", [Constructor( "succ", [Var("E")])], [Constructor( "int", []) ]  )  )
]

let isZero = 
[Rule("isZero",
 				[Formula("typeOf", [Var("E")], [Constructor( "int", []) ] )],
				
 			   	Formula("typeOf", [Constructor( "isZero", [Var("E")])], [Constructor( "bool", []) ]  )  ) 
]
let pred = 
[Rule("pred",
 				[Formula("typeOf", [Var("E")], [Constructor( "int", []) ] )],
				
 			   	Formula("typeOf", [Constructor( "pred", [Var("E")])], [Constructor( "int", []) ]  )  ) 
]

let excValue = 
[Rule("excValue",
				[],
				Formula("typeOf", [Constructor( "excValue", [])], [Constructor( "excType",[])]  )  ) 
]
let tryy = 
[Rule("try",
 				[Formula("typeOf", [Var("E1")] ,  [Var("T")]) ;
 			   	Formula("typeOf", [Var("E2")], [Constructor( "arrow", [Constructor( "excType", []) ; Var("T")]) ]  )],

				Formula("typeOf", [Constructor( "try", [Var("E1") ; Var("E2")])], [Var("T")]  )  )
]
let raise = 
[Rule("raise",
 				[Formula("typeOf", [Var("E")] ,  [Constructor( "excType", [])])],

				Formula("typeOf", [Constructor( "raise", [Var("E")])], [Var("T")])) 
]
let fix = 
[Rule("fix",
				[Formula("typeOf", [Var("E")], [Constructor( "arrow", [Var("T") ; Var("T")]) ]  )],

				Formula("typeOf", [Constructor( "fix", [Var("E")])], [Var("T")]  )  )
]
let tt = 
[Rule("tt",
	   			[],
				Formula("typeOf",     [Constructor( "tt", [])],      [Constructor( "bool", [])]))
]
let ff = 
[Rule("ff",
	   			[],
				Formula("typeOf",     [Constructor( "ff", [])],      [Constructor( "bool", [])]))
]
let iff = 
[Rule("if",
	 			[Formula("typeOf",     [Var("E1")], [Constructor( "bool", []  )]) ;
 				Formula("typeOf", [Var("E2")] ,  [Var("T")]) ;
 			   	Formula("typeOf", [Var("E3")] ,  [Var("T")])],

 			   	Formula("typeOf", [Constructor( "if", [Var("E1") ; Var("E2") ; Var("E3") ])],[Var("T")]  )  )
] 
let absInf = 
[Rule("abs",
 		 		[Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
      		  	Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])]))
]
let lett = 
[Rule("let",
 				[Formula("typeOf", [Var("E")], [Var("T1")]) ; Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],

				Formula("typeOf", [Constructor( "let", [Var("E") ; Var("R")])], [Var("T2")]  )  ) 
]
let letrecc = 
[Rule("letrec",
	 		    [Hypothetical(Var("T1"), Application(Var("R1"), Var("x")), Var("T1"))  ; Hypothetical(Var("T1"), Application(Var("R2"), Var("x")), Var("T2"))],
	 
	 		    Formula("typeOf", [Constructor( "letrec", [Var("R1") ; Var("R2")])], [Var("T2")]  )  ) 
]	
let emptyList =
[Rule("emptyList",
				[],
	
				Formula("typeOf", [Constructor( "emptyList", [])], [Constructor( "list", [Var("T")])])) 
]
let cons = 
[Rule("cons",
				[Formula("typeOf", [Var("E1")] ,  [Var("T")]) ; Formula("typeOf", [Var("E2")] , [Constructor( "list", [Var("T")])]) ],
				
				Formula("typeOf", [Constructor( "cons", [Var("E1") ; Var("E2")])], [Constructor( "list", [Var("T")])])) 
]				
let head = 
[Rule("head",
	 			[Formula("typeOf", [Var("E")], [Constructor( "list", [Var("T")])])],
 
 			   	Formula("typeOf", [Constructor( "head", [Var("E")])], [Var("T")]))
]
let tail = 
[Rule("tail",
	 			[Formula("typeOf", [Var("E")], [Constructor( "list", [Var("T")])])],

				Formula("typeOf", [Constructor( "tail", [Var("E")])], [Constructor( "list", [Var("T")])])) 
]
let isnil = 
[Rule("isnil",
	 			[Formula("typeOf", [Var("E")], [Constructor( "list", [Var("T")])])],

				Formula("typeOf", [Constructor( "isnil", [Var("E")])], [Constructor( "bool", [])])) 
]
let error = 
[Rule("error",
				[],

				Formula("typeOf", [Constructor( "myError", [])], [Var("T")])) 
]			
let pair = 
[Rule("pair",
				[Formula("typeOf", [Var("E1")] ,  [Var("T1")]) ; Formula("typeOf", [Var("E2")] ,  [Var("T2")]) ],
	
				Formula("typeOf", [Constructor( "pair", [Var("E1") ; Var("E2")])], [Constructor( "times", [Var("T1") ; Var("T2")])])) 
]
let fstt = 
[Rule("fst",
		 		[Formula("typeOf", [Var("E")], [Constructor( "times", [Var("T1") ; Var("T2")])])],
	
				Formula("typeOf", [Constructor( "fst", [Var("E")])], [Var("T1")])) 
]
let sndd = 
[Rule("snd",
 				[Formula("typeOf", [Var("E")], [Constructor( "times", [Var("T1") ; Var("T2")])])],
 
 			   	Formula("typeOf", [Constructor( "snd", [Var("E")])], [Var("T2")])) 
]

let inl = 
[Rule("inl",
				[Formula("typeOf", [Var("E")] ,  [Var("T1")]) ],
				Formula("typeOf", [Constructor( "inl", [Var("E")])], [Constructor( "sum", [Var("T1") ; Var("T2")])]))
]
let inr = 
[Rule("inr",
				[Formula("typeOf", [Var("E")] ,  [Var("T2")]) ],
				Formula("typeOf", [Constructor( "inr", [Var("E") ])], [Constructor( "sum", [Var("T1") ; Var("T2")])]))
]
let case = 
[Rule("case",
 				[Formula("typeOf", [Var("EE")], [Constructor( "sum", [Var("T1") ; Var("T2")]) ]  ) ;
  			  	Hypothetical(Var("T1"), Application(Var("R1"), Var("x")), Var("T")) ;
 			   	Hypothetical(Var("T2"), Application(Var("R2"), Var("x")), Var("T"))],

				Formula("typeOf", [Constructor( "case", [Var("EE") ; Var("R1") ; Var("R2")])], [Var("T")]  )  )
]
let tuple5 = 
[Rule("tuple5",
				[Formula("typeOf", [Var("E1")] ,  [Var("T1")]) ; 
				Formula("typeOf", [Var("E2")] ,  [Var("T2")]) ;
				Formula("typeOf", [Var("E3")] ,  [Var("T3")]) ;
				Formula("typeOf", [Var("E4")] ,  [Var("T4")]) ;
				Formula("typeOf", [Var("E5")] ,  [Var("T5")]) ],

				Formula("typeOf", [Constructor( "tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])) 
]
let select1 = 
[Rule("select1",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select1", [Var("E")])], [Var("T1")])) 
]
let select2 = 
[Rule("select2",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select2", [Var("E")])], [Var("T2")])) 
]
let select3 = 
[Rule("select3",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select3", [Var("E")])], [Var("T3")])) 
]
let select4 = 
[Rule("select4",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select4", [Var("E")])], [Var("T4")])) 
]
let select5 = 
[Rule("select5",
 [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
 Formula("typeOf", [Constructor( "select5", [Var("E")])], [Var("T5")])) 
]
let unitt = 
[Rule("unit",
				[],
		    	Formula("typeOf", [Constructor( "unit", [])], [Constructor( "unitType", [])])) 
]
let absT = 
[Rule("absT",
   			[Generic(Application(Var("R2"), Var("x")), Application(Var("R"), Var("x")))],
   		 	Formula("typeOf",     [Constructor( "absT", [Var("R2")])],      [Constructor( "all", [(Var "R")])])) ;
]
let appT = 
[Rule("appT",
 			[Formula("typeOf",[Var("E")],[Constructor("all", [Var("R")])]) ],

			Formula("typeOf",  [Constructor( "appT", [Var("E") ; Var("X")])],    [Application(Var("R"),Var("X"))]  )  ) 
]

(* Some reduction rules *)

let beta = 
[Rule("beta",
				[Formula("value", [Var("EE")], [])],
		    	Formula("step", 
						[Constructor( "app", [Constructor( "abs", [Var("R") ; Var("T")]) ; Var("EE")])],
						[Application(Var("R"), Var("EE"))]  )  ) 
]
let betaImplicit = 
			[Rule("beta",
				[Formula("value", [Var("EE")], [])],
		    	Formula("step", 
						[Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
						[Application(Var("R"), Var("EE"))]  )  ) 
			]  
let ifSemantics = 
   		[
		Rule("conditional_true",
	    	[],
	    	Formula("step",
		    	[Constructor( "if", [Constructor( "tt", []) ; Var("E1") ; Var("E2")])],
		   		[Var("E1")]  )  ) 
				;
		Rule("conditional_false",
	    	[],
	    	Formula("step",
				[Constructor( "if", [Constructor( "ff", []) ; Var("E1") ; Var("E2")])],
					[Var("E2")]  )  ) 
		] 
let fixSemantics = 
		[
		Rule("fixStep",
			[Formula("value", [Var("V")], [])],
			Formula("step",
				[Constructor( "fix", [Var("V")])],
					[Constructor( "app", [Var("V") ; Constructor( "fix", [Var("V")])])]  )  )
		]
let letSemantics = 
		[
		Rule("letStep",
			[Formula("value", [Var("V")], [])],
			Formula("step",
				[Constructor( "let", [Var("V") ; Var("R")])],
				[Application(Var("R"), Var("V"))]  )  )
		]
let headSemantics = 
		[
		Rule("headStepEmpty",
			[],
			Formula("step",
				[Constructor( "head", [Constructor( "emptyList", [])])],
				[Constructor( "myError", [])] ) ) 
				;
		Rule("headStepCons",
			[],
			Formula("step",
				[Constructor( "head", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
				[Var("E1")] ) )
		]   	
let tailSemantics = 
		[
		Rule("tailStepEmpty",
			[],
			Formula("step",
				[Constructor( "tail", [Constructor( "emptyList", [])])],
				[Constructor( "myError", [])] ) ) 
				;
		Rule("tailStepCons",
			[],
			Formula("step",
				[Constructor( "tail", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
				[Var("E2")] ) )
		]  
let isnilSemantics = 
		[
		Rule("isnilStepEmpty",
			[],
			Formula("step",
				[Constructor( "isnil", [Constructor( "emptyList", [])])],
				[Constructor( "tt", [])] ) ) 
				;
		Rule("isnilStepCons",
			[],
			Formula("step",
				[Constructor( "isnil", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
				[Constructor( "ff", [])] ) )
		]  
let appTSemantics = 
		[
		Rule("betaT",
 	   		[],
 		   	Formula("step",
				[Constructor( "appT", [Constructor( "absT", [Var("R2")]) ; Var("X")])],
    			[Application(Var("R2"), Var("X"))]  )  ) 
		]
(* Typed Languages *)
		
let stlc_cbv = TypeSystem(	
					arrow_decl, 
					abs_decl @ app_decl,
					abs @ app @ beta)
					
let stlc_cbv_exc = 
let exceptionSemantics = 
 		[
		Rule("tryValue",
  	  			[Formula("value", [Var("E1")], [])],
  			  	Formula("step",
  					[Constructor( "try", [Var("E1") ; Var("E2")])],
					[Var("E1")]  )  ) ;			
     	Rule("tryError",
    			[],
    			Formula("step",
    				[Constructor( "try", [Constructor( "raise", [Var("E1")]) ; Var("E2")])],
					[Constructor( "app",[Var("E2") ; Var("E1")])]  )  )			
		] in 
			TypeSystem(
					arrow_decl @ excType_decl,	
					abs_decl @ excValue_decl @ app_decl @ try_decl @ raise_decl, 
					abs @ excValue @ app @ tryy @ raise @ beta @ exceptionSemantics)


let stlc_cbv_fix = 
			TypeSystem(
					arrow_decl,
					abs_decl @ app_decl @ fix_decl,
					abs @ app @ fix @ beta @ fixSemantics)
	       
let stlc_cbv_if = 
			TypeSystem(
				arrow_decl @ bool_decl,
				abs_decl @ true_decl @ false_decl @ app_decl @ if_decl,
				abs @ tt @ ff @ app @ iff @ beta @ ifSemantics)	       

let stlc_cbv_integers = 
let isZeroSemantics = 
		[
		Rule("isZeroZero",
				[],
				Formula("step",
					[Constructor( "isZero", [Constructor( "zero", [])])],
					[Constructor( "tt", [])] ) )
		;				
		Rule("isZeroSucc",
				[],
				Formula("step",
					[Constructor( "isZero", [Constructor( "succ", [Var("E")])])],
					[Constructor( "ff", [])] ) )
		] in 
let predSemantics = 
		[
		Rule("predZero",
				[],
				Formula("step",
					[Constructor( "pred", [Constructor( "zero", [])])],
					[Constructor( "zero", [])] ) )
		;				
		Rule("predSucc",
				[],
				Formula("step",
					[Constructor( "pred", [Constructor( "succ", [Var("E")])])],
					[Var("E")] ) )
		] in 
			TypeSystem( 
		   			arrow_decl @ bool_decl @ int_decl,
					abs_decl @ zero_decl @ succ_decl @ true_decl @ false_decl @ app_decl @ isZero_decl @ pred_decl,
					abs @ zero @ succ @ tt @ ff @  app @  isZero @  pred @ beta @ isZeroSemantics @ predSemantics)

let stlc_cbv_inf = 
			TypeSystem(
				arrow_decl,
				absInf_decl @  app_decl,
				absInf @ app @ betaImplicit)

let stlc_cbv_let = 
			TypeSystem(
			   arrow_decl,
			   abs_decl @ app_decl @ let_decl,
			   abs @ app @ lett @ beta @ letSemantics)

let stlc_cbv_letrec = 
let letrecSemantics = 
		[
		Rule("letrecStep",
			[],
			Formula("step",
				[Constructor( "letrec", [Var("R1") ; Var("R2")])],
				[Constructor( "let", [Constructor( "fix", [Constructor( "abs", [Var("R1")])]) ; Var("R2")])]  )  )
		] in TypeSystem(
				arrow_decl, 
				absInf_decl @ app_decl @ let_decl @ letrec_decl @ fix_decl, 
				absInf @ app @ lett @ letrecc @ fix @ betaImplicit @ letSemantics @ letrecSemantics @ fixSemantics)
			  

let stlc_cbv_lists = 
			TypeSystem(
				arrow_decl @ list_decl,
				abs_decl @ emptyList_decl @ cons_decl @ app_decl @ head_decl @ tail_decl @ myError_decl, 
				abs @ emptyList @ cons @ app @ head @ tail @ error @ beta @ headSemantics @ tailSemantics)

let stlc_cbv_pairs = 
let pairSemantics = 
		[
		Rule("fstStep",
	    	[],
	    	Formula("step",
				[Constructor( "fst", [Constructor( "pair", [Var("E1") ; Var("E2")])])],
				[Var("E1")]  )  ) 
				;				
		Rule("sndStep",
 			[],
			Formula("step",
				[Constructor( "snd", [Constructor( "pair", [Var("E1") ; Var("E2")])])],
				[Var("E2")]  )  ) 				
		] in TypeSystem(
				arrow_decl @ times_decl,
				abs_decl @ pair_decl @ app_decl @ fst_decl @ snd_decl,
				abs @ pair @ app @ fstt @ sndd @ beta @ pairSemantics)

let stlc_cbv_sum = 
let caseSemantics = 
		[
		Rule("caseStepinl",
			[],
			Formula("step",
				[Constructor( "case", [Constructor( "inl", [Var("EE")]) ; Var("R1") ; Var("R2")])],
				[Application(Var("R1"), Var("EE"))]  )  ) 
				;		
		Rule("caseStepinr",
			[],
			Formula("step",
				[Constructor( "case", [Constructor( "inr", [Var("EE")]) ; Var("R1") ; Var("R2")])],
				[Application(Var("R2"), Var("EE"))]  )  ) 				
		] in TypeSystem(
				arrow_decl @ sum_decl, 
				abs_decl @ inl_decl @ inr_decl @ app_decl @ case_decl, 
				abs @ inl @ inr @ app @ case @ beta @ caseSemantics)

let stlc_cbv_tuples = 
let arity = 5 in 
let arityArray = range 1 arity in 
let eVars = List.map toVar (getFormalVariables "E" arity) in let tVars = List.map toVar (getFormalVariables "T" arity) in 
let oneTypeRule i = Rule(
						"select" ^ (string_of_int i), 
						[Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
						Formula("typeOf", [Constructor( "select" ^ (string_of_int i), [Var("E")])], [Var("T" ^ (string_of_int i))]))
					in 
let oneStepRule i = Rule(
						"select" ^ (string_of_int i) ^ "Step", 
						[],
						Formula("step", [Constructor( "select" ^ (string_of_int i), [Constructor("tuple" ^ (string_of_int arity), eVars)])], [Var("E" ^ (string_of_int i))]))
					in 
let tupleTypingRule = 
	let oneFormula = fun i -> Formula("typeOf", [Var("E" ^ (string_of_int i))] ,  [Var("T" ^ (string_of_int i))]) in 
					[
					Rule(
						"tuple" ^ (string_of_int arity),
						List.map oneFormula arityArray, 
						Formula("typeOf", [Constructor("tuple" ^ (string_of_int arity), eVars)], [Constructor("times" ^ (string_of_int arity), tVars)]))
					] in 
let timesDeclaration =  [DeclType("times" ^ (string_of_int arity), repeat (Simple("typ")) arity)] in 
let tupleDeclaration =  [DeclTrm("tuple" ^ (string_of_int arity), Constr ("times" ^ (string_of_int arity)), Contextual [], repeat (Simple("term")) arity)] in 
let selectDeclarations = List.map (fun i -> DeclTrm("select" ^ (string_of_int i), Destr ("times" ^ (string_of_int arity)), Contextual [(1,[])], [Simple("term")])) arityArray in
let selectTypingRules = List.map oneTypeRule arityArray in 
let selectSemantics = List.map oneStepRule arityArray in 
			TypeSystem(
				arrow_decl @ timesDeclaration,
				abs_decl @ tupleDeclaration @ app_decl @ selectDeclarations, 
				abs @ tupleTypingRule @ app @ selectTypingRules @ beta @ selectSemantics)

let stlc_cbv_unit = 
			TypeSystem(
				arrow_decl @ unitType_decl, 
				abs_decl @ unit_decl @ app_decl,
				abs @ unitt @ app @ beta)


let systemF_cbv = 
			TypeSystem(
				arrow_decl @ all_decl, 
				abs_decl @ absT_decl @ app_decl @ appT_decl,
				abs @ absT @ app @ appT @ beta @ appTSemantics)
			

let fullFledged_cbv = 
			TypeSystem(
				   arrow_decl @ bool_decl @ list_decl @ all_decl, 
				   abs_decl @ true_decl @ false_decl @ emptyList_decl @ cons_decl @ absT_decl @ app_decl @ if_decl @ head_decl @ tail_decl @ isnil_decl @ appT_decl @ let_decl @ myError_decl, 
				   abs @ tt @ ff @ emptyList @ cons @ absT @ app @ iff @ head @ tail @ isnil @ appT @ lett @ error @ beta @ ifSemantics @ headSemantics @ tailSemantics @ isnilSemantics @ appTSemantics @ letSemantics)

*)