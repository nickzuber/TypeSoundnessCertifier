
open Type_system

let emptyTS = TypeSystem([], [], [])

let stlc_cbv = TypeSystem(
			   [
		   		DeclType("arrow", [Simple("typ") ; Simple("typ")]) ; 
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term") ; Simple("typ") ]);
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R") ; Var("T1")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R") ; Var("T")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
	      ])

		  (* stlc_add is not in the tested calculi now *)
let stlc_cbv_add = TypeSystem(
			   [
		   		DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
		   		DeclType("int", []) 
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("succ", Constr "int", Contextual [(1,[])], [Simple("term")]) ;
					DeclTrm("zero", Constr "int", Contextual [], []) ;
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("add", Destr "int", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
   	       Rule("succ",
   		    [Formula("typeOf", [Var("E")], [Constructor( "int", []) ]  ) ;
   		    ],
   		    Formula("typeOf", [Constructor( "succ", [Var("E")])], [Constructor( "int", []) ]  )  ) ;
    	       Rule("zero",
    		    [],
    		    Formula("typeOf", [Constructor( "zero", [])], [Constructor( "int", []) ]  )  ) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
 	       Rule("add",
 		    [Formula("typeOf", [Var("E1")], [Constructor( "int", []) ] ) ;
 		     Formula("typeOf", [Var("E2")], [Constructor( "int", [])]) 
 		    ],
 		    Formula("typeOf", [Constructor( "add", [Var("E1") ; Var("E2")])], [Constructor( "int", []) ]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
	       Rule("addZero",
		    [],
		    Formula("step",
			    [Constructor( "add", [Constructor( "zero", []) ; Var("E")])],
			    [Var("E")]  )  ) ;				
	 	       Rule("addSucc",
	 		    [],
	 		    Formula("step",
	 			    [Constructor( "add", [Constructor( "succ", [Var("E1")]) ; Var("E2")])],
	 			    [Var("E1+E2")]  )  ) ;				
	      ])

let stlc_cbv_exc = TypeSystem(
			   [
		   		DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
		   		DeclType("excType", []) 
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("excValue", Constr "excType", Contextual [], []) ;
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("try", ErrorHandler, Contextual [(1,[])], [Simple("term"); Simple("term")]) ;
					DeclTrm("raise", Error, Contextual [(1,[])], [Simple("term")]) ;					
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
   		   Rule("excValue",
   		   		[],
   				Formula("typeOf", [Constructor( "excValue", [])], [Constructor( "excType",[])]  )  ) ;
		   Rule("app",
		   		[Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
				 Formula("typeOf", [Var("E2")] ,  [Var("T1")])
				 ],
				 Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
 	       Rule("try",
 		    [Formula("typeOf", [Var("E1")] ,  [Var("T")]) ;
			 Formula("typeOf", [Var("E2")], [Constructor( "arrow", [Constructor( "excType", []) ; Var("T")]) ]  ) 		    
			 ],
		    Formula("typeOf", [Constructor( "try", [Var("E1") ; Var("E2")])], [Var("T")]  )  ) ;
  	       Rule("raise",
  		    [Formula("typeOf", [Var("E")] ,  [Constructor( "excType", [])])],
 		    Formula("typeOf", [Constructor( "raise", [Var("E")])], [Var("T")])) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
	       Rule("tryValue",
		    [Formula("value", [Var("E1")], [])],
		    Formula("step",
		    	[Constructor( "try", [Var("E1") ; Var("E2")])],
				[Var("E1")]  )  ) ;				
	 	       Rule("tryError",
	 		    [],
	 		    Formula("step",
	 		    	[Constructor( "try", [Constructor( "raise", [Var("E1")]) ; Var("E2")])],
	 				[Constructor( "app",[Var("E2") ; Var("E1")])]  )  ) ;				
	      ])


let stlc_cbv_fix = TypeSystem(
			   [
		   		DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("fix", Derived (Some "arrow"), Contextual [(1,[])], [Simple("term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
 	       Rule("fix",
 		    [Formula("typeOf", [Var("E")], [Constructor( "arrow", [Var("T") ; Var("T")]) ]  ) ;
 		    ],
 		    Formula("typeOf", [Constructor( "fix", [Var("E")])], [Var("T")]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
			Rule("fixStep",
			[Formula("value", [Var("V")], [])],
			Formula("step",
			[Constructor( "fix", [Var("V")])],
			[Constructor( "app", [Var("V") ; Constructor( "fix", [Var("V")])])]  )  ) ;				
	      ])
	       
let stlc_cbv_if = TypeSystem(
			   [
		   		DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
			   	DeclType("bool", []) ;
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("tt", Constr "bool", Contextual [], []);
					DeclTrm("ff", Constr "bool", Contextual [], []);
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("if", Destr "bool", Contextual [(1,[]) ; (2,[1]) ; (3,[1 ; 2])], [Simple("term") ; Simple("term") ; Simple("term")]);
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
 	       Rule("tt",
 	          [],
 	          Formula("typeOf",     [Constructor( "tt", [])],      [Constructor( "bool", [])])) ;
 	       Rule("ff",
 	          [],
 	          Formula("typeOf",     [Constructor( "ff", [])],      [Constructor( "bool", [])])) ;
   	       Rule("app",
   		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
   		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
   		    ],
   		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
 	       Rule("if",
 		    [Formula("typeOf",     [Var("E1")],
 			     [Constructor( "bool", []  )]) ;
 		    Formula("typeOf", [Var("E2")] ,  [Var("T")]) ;
 		    Formula("typeOf", [Var("E3")] ,  [Var("T")]) ;
 		    ],
 		    Formula("typeOf",
 			    [Constructor( "if", [Var("E1") ;
 					          Var("E2") ; Var("E3") ])],
 			    [Var("T")]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
	 	       Rule("conditional_true",
	 		    [],
	 		    Formula("step",
	 			    [Constructor( "if", [Constructor( "tt", []) ; Var("E1") ; Var("E2")])],
	 			    [Var("E1")]  )  ) ;

	 	       Rule("conditional_false",
	 		    [],
	 		    Formula("step",
	 			    [Constructor( "if", [Constructor( "ff", []) ; Var("E1") ; Var("E2")])],
	 			    [Var("E2")]  )  ) ;
	      ])
	       

let stlc_cbv_inf = TypeSystem(
			   [
		   		DeclType("arrow", [Simple("typ") ; Simple("typ")]) ; 
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
	      ])


let stlc_cbv_let = TypeSystem(
			   [
		   		DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("let", Derived None, Contextual [(1,[])], [Simple("term") ; Abstraction("term", "term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
 	       Rule("let",
 		    [Formula("typeOf", [Var("E")], [Var("T1")]) ; Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2")) 
 		    ],
 		    Formula("typeOf", [Constructor( "let", [Var("E") ; Var("R")])], [Var("T2")]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
			Rule("letStep",
				[Formula("value", [Var("V")], [])],
				Formula("step",
				[Constructor( "let", [Var("V") ; Var("R")])],
				[Application(Var("R"), Var("V"))]  )  ) ;				
	      ])

let stlc_cbv_letrec = TypeSystem(
				   [
			   		DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
					],
					[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
						DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
						DeclTrm("let", Derived None, Contextual [(1,[])], [Simple("term") ; Abstraction("term", "term")]) ;
						DeclTrm("letrec", Derived None, Contextual [], [Abstraction("term", "term") ; Abstraction("term", "term")]) ;
						DeclTrm("fix", Derived (Some "arrow"), Contextual [(1,[])], [Simple("term")]) ;
		   			],
		    [  Rule("abs",
		          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
		          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
		       Rule("app",
			    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
			     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
			    ],
			    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
	 	       Rule("let",
	 		    [Formula("typeOf", [Var("E")], [Var("T1")]) ; Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2")) 
	 		    ],
	 		    Formula("typeOf", [Constructor( "let", [Var("E") ; Var("R")])], [Var("T2")]  )  ) ;
	 	       Rule("letrec",
	 		    [Hypothetical(Var("T1"), Application(Var("R1"), Var("x")), Var("T1"))  ; Hypothetical(Var("T1"), Application(Var("R2"), Var("x")), Var("T2")) 
	 		    ],
	 		    Formula("typeOf", [Constructor( "letrec", [Var("R1") ; Var("R2")])], [Var("T2")]  )  ) ;
	 	       Rule("fix",
	 		    [Formula("typeOf", [Var("E")], [Constructor( "arrow", [Var("T") ; Var("T")]) ]  ) ;
	 		    ],
	 		    Formula("typeOf", [Constructor( "fix", [Var("E")])], [Var("T")]  )  ) ;
		       Rule("beta",
   	    		[Formula("value", [Var("EE")], [])],
			    Formula("step",
				    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
				    [Application(Var("R"), Var("EE"))]  )  ) ;				
   			Rule("letStep",
   				[Formula("value", [Var("V")], [])],
   				Formula("step",
   				[Constructor( "let", [Var("V") ; Var("R")])],
   				[Application(Var("R"), Var("V"))]  )  ) ;				
	   		Rule("letrecStep",
	   				[],
	   				Formula("step",
	   				[Constructor( "letrec", [Var("R1") ; Var("R2")])],
					[Constructor( "let", [Constructor( "fix", [Constructor( "abs", [Var("R1")])]) ; Var("R2")])]  )  ) ;				
  			Rule("fixStep",
  			[Formula("value", [Var("V")], [])],
  			Formula("step",
  			[Constructor( "fix", [Var("V")])],
  			[Constructor( "app", [Var("V") ; Constructor( "fix", [Var("V")])])]  )  ) ;				
		  	])
			  

let stlc_cbv_lists = TypeSystem(
			   [
	   			DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
				DeclType("list", [Simple("typ")]) ;
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("emptyList", Constr "list", Contextual [], []);
					DeclTrm("cons", Constr "list", Contextual [], [Simple("term"); Simple("term")]);
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("head", Destr "list", Contextual [(1,[])], [Simple("term")]) ;
					DeclTrm("myError", Error , Contextual [], []) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
		   Rule("emptyList",
   		   	[],
   		   	Formula("typeOf", [Constructor( "emptyList", [])], [Constructor( "list", [Var("T")])])) ;
      	   Rule("cons",
 		   	[Formula("typeOf", [Var("E1")] ,  [Var("T")]) ; Formula("typeOf", [Var("E2")] , [Constructor( "list", [Var("T")])]) ],
 		   	Formula("typeOf", [Constructor( "cons", [Var("E1") ; Var("E2")])], [Constructor( "list", [Var("T")])])) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
  	       Rule("head",
  		    [Formula("typeOf", [Var("E")], [Constructor( "list", [Var("T")])])],
  		    Formula("typeOf", [Constructor( "head", [Var("E")])], [Var("T")])) ;
		   Rule("error",
   		   	[],
   		   	Formula("typeOf", [Constructor( "myError", [])], [Var("T")])) ;
(*  	       Rule("tail",
   		    [Formula("typeOf", [Var("E")], [Constructor( "list", [Var("T")])])],
   		    Formula("typeOf", [Constructor( "tail", [Var("E")])], [Constructor( "list", [Var("T")])])) ;
*)
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
			Rule("headStepEmpty",
			[],
			Formula("step",
			[Constructor( "head", [Constructor( "emptyList", [])])],
			[Constructor( "myError", [])] ) ) ;
			Rule("headStepCons",
			[],
			Formula("step",
			[Constructor( "head", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
			[Var("E1")] ) ) ;				
	      ])

let stlc_cbv_pairs = TypeSystem(
			   [
	   			DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
				DeclType("times", [Simple("typ") ; Simple("typ")]) ;
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("pair", Constr "times", Contextual [], [Simple("term"); Simple("term")]);
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("fst", Destr "times", Contextual [(1,[])], [Simple("term")]) ;
					DeclTrm("snd", Destr "times", Contextual [(1,[])], [Simple("term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
      	   Rule("pair",
 		   	[Formula("typeOf", [Var("E1")] ,  [Var("T1")]) ; Formula("typeOf", [Var("E2")] ,  [Var("T2")]) ],
 		   	Formula("typeOf", [Constructor( "pair", [Var("E1") ; Var("E2")])], [Constructor( "times", [Var("T1") ; Var("T2")])])) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
  	       Rule("fst",
  		    [Formula("typeOf", [Var("E")], [Constructor( "times", [Var("T1") ; Var("T2")])])],
  		    Formula("typeOf", [Constructor( "fst", [Var("E")])], [Var("T1")])) ;
   	       Rule("snd",
   		    [Formula("typeOf", [Var("E")], [Constructor( "times", [Var("T1") ; Var("T2")])])],
   		    Formula("typeOf", [Constructor( "snd", [Var("E")])], [Var("T2")])) ;
 	       Rule("beta",
   		 	[Formula("value", [Var("EE")], [])],
 		    Formula("step",
 			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
 			    [Application(Var("R"), Var("EE"))]  )  ) ;				
			Rule("fstStep",
	 		    [],
	 		    Formula("step",
				[Constructor( "fst", [Constructor( "pair", [Var("E1") ; Var("E2")])])],
				[Var("E1")]  )  ) ;				
			Rule("sndStep",
		 		[],
				Formula("step",
				[Constructor( "snd", [Constructor( "pair", [Var("E1") ; Var("E2")])])],
				[Var("E2")]  )  ) ;				
	      ])

let stlc_cbv_sum = TypeSystem(
			   [
					DeclType("arrow", [Simple("typ") ; Simple("typ")]) ; 
	   				DeclType("sum", [Simple("typ") ; Simple("typ")]) ; 
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term") ; Simple("typ") ]);
					DeclTrm("inl", Constr "sum", Contextual [], [Simple("term")]) ;
					DeclTrm("inr", Constr "sum", Contextual [], [Simple("term")]) ;
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("case", Destr "sum", Contextual [(1,[])], [Simple("term"); Abstraction("term", "term") ; Abstraction("term", "term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R") ; Var("T1")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
      	   Rule("inl",
 		   	[Formula("typeOf", [Var("E")] ,  [Var("T1")]) ],
 		   	Formula("typeOf", [Constructor( "inl", [Var("E")])], [Constructor( "sum", [Var("T1") ; Var("T2")])])) ;
      	   Rule("inr",
 		   	[Formula("typeOf", [Var("E")] ,  [Var("T2")]) ],
 		   	Formula("typeOf", [Constructor( "inr", [Var("E") ])], [Constructor( "sum", [Var("T1") ; Var("T2")])])) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
	       Rule("case",
		    [Formula("typeOf", [Var("EE")], [Constructor( "sum", [Var("T1") ; Var("T2")]) ]  ) ;
		     Hypothetical(Var("T1"), Application(Var("R1"), Var("x")), Var("T")) ;
			 Hypothetical(Var("T2"), Application(Var("R2"), Var("x")), Var("T"))
		    ],
		    Formula("typeOf", [Constructor( "case", [Var("EE") ; Var("R1") ; Var("R2")])], [Var("T")]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R") ; Var("T")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
 	       Rule("caseStepinl",
		    [],
		    Formula("step",
			    [Constructor( "case", [Constructor( "inl", [Var("EE")]) ; Var("R1") ; Var("R2")])],
			    [Application(Var("R1"), Var("EE"))]  )  ) ;		
 	       Rule("caseStepinr",
		    [],
		    Formula("step",
			    [Constructor( "case", [Constructor( "inr", [Var("EE")]) ; Var("R1") ; Var("R2")])],
			    [Application(Var("R2"), Var("EE"))]  )  ) ;				
	      ])


let stlc_cbv_tuples = TypeSystem(
			   [
	   			DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
				DeclType("times5", [Simple("typ") ; Simple("typ") ; Simple("typ") ; Simple("typ") ; Simple("typ")]) ;
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("tuple5", Constr "times5", Contextual [], [Simple("term") ; Simple("term") ; Simple("term") ; Simple("term") ; Simple("term") ]);
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("select1", Destr "times5", Contextual [(1,[])], [Simple("term")]) ;
					DeclTrm("select2", Destr "times5", Contextual [(1,[])], [Simple("term")]) ;
					DeclTrm("select3", Destr "times5", Contextual [(1,[])], [Simple("term")]) ;
					DeclTrm("select4", Destr "times5", Contextual [(1,[])], [Simple("term")]) ;
					DeclTrm("select5", Destr "times5", Contextual [(1,[])], [Simple("term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
      	   Rule("tuple5",
 		   	[Formula("typeOf", [Var("E1")] ,  [Var("T1")]) ; 
			 Formula("typeOf", [Var("E2")] ,  [Var("T2")]) ;
			 Formula("typeOf", [Var("E3")] ,  [Var("T3")]) ;
			 Formula("typeOf", [Var("E4")] ,  [Var("T4")]) ;
			 Formula("typeOf", [Var("E5")] ,  [Var("T5")]) ;
			],
 		   	Formula("typeOf", [Constructor( "tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])) ;
	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
  	       Rule("select1",
  		    [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
  		    Formula("typeOf", [Constructor( "select1", [Var("E")])], [Var("T1")])) ;
   	       Rule("select2",
   		    [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
   		    Formula("typeOf", [Constructor( "select2", [Var("E")])], [Var("T2")])) ;
   	       Rule("select3",
   		    [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
   		    Formula("typeOf", [Constructor( "select3", [Var("E")])], [Var("T3")])) ;
   	       Rule("select4",
   		    [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
   		    Formula("typeOf", [Constructor( "select4", [Var("E")])], [Var("T4")])) ;
   	       Rule("select5",
   		    [Formula("typeOf", [Var("E")], [Constructor( "times5", [Var("T1") ; Var("T2") ; Var("T3") ; Var("T4") ; Var("T5") ])])],
   		    Formula("typeOf", [Constructor( "select5", [Var("E")])], [Var("T5")])) ;
 	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
 		    Formula("step",
 			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("EE")])],
 			    [Application(Var("R"), Var("EE"))]  )  ) ;				
			Rule("select1Step",
	 		    [],
	 		    Formula("step",
				[Constructor( "select1", [Constructor( "tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])],
				[Var("E1")]  )  ) ;				
			Rule("select2Step",
	 		    [],
	 		    Formula("step",
				[Constructor( "select2", [Constructor( "tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])],
				[Var("E2")]  )  ) ;				
			Rule("select3Step",
	 		    [],
	 		    Formula("step",
				[Constructor( "select3", [Constructor( "tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])],
				[Var("E3")]  )  ) ;				
			Rule("select4Step",
	 		    [],
	 		    Formula("step",
				[Constructor( "select4", [Constructor( "tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])],
				[Var("E4")]  )  ) ;				
			Rule("select5Step",
	 		    [],
	 		    Formula("step",
				[Constructor( "select5", [Constructor( "tuple5", [Var("E1") ; Var("E2") ; Var("E3") ; Var("E4") ; Var("E5") ])])],
				[Var("E5")]  )  ) ;				
	      ])

let stlc_cbv_unit = TypeSystem(
			   [
	   				DeclType("arrow", [Simple("typ") ; Simple("typ")]) ; 
	   				DeclType("unitType", []) ; 
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term") ; Simple("typ") ]);
					DeclTrm("unit", Constr "unitType", Contextual [], []) ;
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R") ; Var("T1")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
	       Rule("unit",
		    [],
		    Formula("typeOf", [Constructor( "unit", [])], [Constructor( "unitType", [])])) ;
 	       Rule("app",
		    [Formula("typeOf", [Var("E1")], [Constructor( "arrow", [Var("T1") ; Var("T2")]) ]  ) ;
		     Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf", [Constructor( "app", [Var("E1") ; Var("E2")])], [Var("T2")]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R") ; Var("T")]) ; Var("EE")])],
			    [Application(Var("R"), Var("EE"))]  )  ) ;				
	      ])

let systemF_cbv = TypeSystem(
			   [
			   	DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
			   	DeclType("all", [Abstraction("typ", "typ")]) 
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("absT", Constr "all", Contextual [], [Abstraction("typ", "term")]) ;
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("appT", Destr "all", Contextual [(1,[])], [Simple("term"); Simple("typ")]) 
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
	       Rule("absT",
	          [Generic(Application(Var("R2"), Var("x")), Application(Var("R"), Var("x")))],
	          Formula("typeOf",     [Constructor( "absT", [Var("R2")])],      [Constructor( "all", [(Var "R")])])) ;
	       Rule("app",
		    [Formula("typeOf",     [Var("E1")],
			     [Constructor( "arrow", [Var("T1") ;
					             Var("T2")]  )  ]  ) ;
		    Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf",
			    [Constructor( "app", [Var("E1") ;
					          Var("E2")])],
			    [Var("T2")]  )  ) ;
	       Rule("appT",
		    [Formula("typeOf",     [Var("E")],
			     [Constructor("all", [Var("R")])]) 
		    ],
		    Formula("typeOf",
			    [Constructor( "appT", [Var("E") ;
					          Var("X")])],
			    [Application(Var("R"),Var("X"))]  )  ) ;
	       Rule("beta",
    		[Formula("value", [Var("EE")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("APPLIED")])],
			    [Application(Var("R"), Var("APPLIED"))]  )  ) ;
	       Rule("betaT",
		    [],
		    Formula("step",
			    [Constructor( "appT", [Constructor( "absT", [Var("R2")]) ; Var("X")])],
			    [Application(Var("R2"), Var("X"))]  )  ) 
		    ])

let fullFledged_cbv = TypeSystem(
			   [
			   	DeclType("arrow", [Simple("typ") ; Simple("typ")]) ;
			   	DeclType("bool", []) ;
				DeclType("list", [Simple("typ")]) ;
			   	DeclType("all", [Abstraction("typ", "typ")]) 
				],
				[   DeclTrm("abs", Constr "arrow", Contextual [], [Abstraction("term", "term")]);
					DeclTrm("tt", Constr "bool", Contextual [], []);
					DeclTrm("ff", Constr "bool", Contextual [], []);
					DeclTrm("emptyList", Constr "list", Contextual [], []);
					DeclTrm("cons", Constr "list", Contextual [], [Simple("term"); Simple("term")]);
					DeclTrm("absT", Constr "all", Contextual [], [Abstraction("typ", "term")]) ;
					DeclTrm("app", Destr "arrow", Contextual [(1,[]) ; (2,[1])], [Simple("term"); Simple("term")]) ;
					DeclTrm("if", Destr "bool", Contextual [(1,[]) ; (2,[1]) ; (3,[1 ; 2])], [Simple("term") ; Simple("term") ; Simple("term")]);
					DeclTrm("head", Destr "list", Contextual [(1,[])], [Simple("term")]) ;
					DeclTrm("appT", Destr "all", Contextual [(1,[])], [Simple("term"); Simple("typ")]) ;
					DeclTrm("let", Derived None, Contextual [(1,[])], [Simple("term") ; Abstraction("term", "term")]) ;
					DeclTrm("myError", Error , Contextual [], []) ;
	   			],
	    [  Rule("abs",
	          [Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2"))],
	          Formula("typeOf",     [Constructor( "abs", [Var("R")])],      [Constructor( "arrow", [(Var "T1") ; (Var "T2")])])) ;
 	       Rule("tt",
 	          [],
 	          Formula("typeOf",     [Constructor( "tt", [])],      [Constructor( "bool", [])])) ;
 	       Rule("ff",
 	          [],
 	          Formula("typeOf",     [Constructor( "ff", [])],      [Constructor( "bool", [])])) ;
		   Rule("emptyList",
   		   	[],
   		   	Formula("typeOf", [Constructor( "emptyList", [])], [Constructor( "list", [Var("T")])])) ;
      	   Rule("cons",
 		   	[Formula("typeOf", [Var("E1")] ,  [Var("T")]) ; Formula("typeOf", [Var("E2")] , [Constructor( "list", [Var("T")])]) ],
 		   	Formula("typeOf", [Constructor( "cons", [Var("E1") ; Var("E2")])], [Constructor( "list", [Var("T")])])) ;
		   Rule("absT",
	          [Generic(Application(Var("R2"), Var("x")), Application(Var("R"), Var("x")))],
	          Formula("typeOf",     [Constructor( "absT", [Var("R2")])],      [Constructor( "all", [(Var "R")])])) ;
	       Rule("app",
		    [Formula("typeOf",     [Var("E1")],
			     [Constructor( "arrow", [Var("T1") ;
					             Var("T2")]  )  ]  ) ;
		    Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf",
			    [Constructor( "app", [Var("E1") ;
					          Var("E2")])],
			    [Var("T2")]  )  ) ;
	       Rule("appT",
		    [Formula("typeOf",     [Var("E")],
			     [Constructor("all", [Var("R")])]) 
		    ],
		    Formula("typeOf",
			    [Constructor( "appT", [Var("E") ;
					          Var("X")])],
			    [Application(Var("R"),Var("X"))]  )  ) ;
 	       Rule("let",
 		    [Formula("typeOf", [Var("E")], [Var("T1")]) ; Hypothetical(Var("T1"), Application(Var("R"), Var("x")), Var("T2")) 
 		    ],
 		    Formula("typeOf", [Constructor( "let", [Var("E") ; Var("R")])], [Var("T2")]  )  ) ;
		   Rule("error",
   		   	[],
   		   	Formula("typeOf", [Constructor( "myError", [])], [Var("T")])) ;
 	       Rule("beta",
	    	[Formula("value", [Var("EE")], [])],
 		    Formula("step",
 			    [Constructor( "app", [Constructor( "abs", [Var("R") ; Var("T")]) ; Var("EE")])],
 			    [Application(Var("R"), Var("EE"))]  )  ) ;				
	 	   Rule("conditional_true",
	 		    [],
	 		    Formula("step",
	 			    [Constructor( "if", [Constructor( "tt", []) ; Var("E1") ; Var("E2")])],
	 			    [Var("E1")]  )  ) ;
	 	   Rule("conditional_false",
	 		    [],
	 		    Formula("step",
	 			    [Constructor( "if", [Constructor( "ff", []) ; Var("E1") ; Var("E2")])],
	 			    [Var("E2")]  )  ) ;
			Rule("headStepEmpty",
					[],
				Formula("step",
					[Constructor( "head", [Constructor( "emptyList", [])])],
					[Constructor( "myError", [])] ) ) ;
			Rule("headStepCons",
				[],
				Formula("step",
					[Constructor( "head", [Constructor( "cons", [Var("E1") ; Var("E2")])])],
					[Var("E1")] ) ) ;				
		   Rule("betaT",
		    [],
		    Formula("step",
			    [Constructor( "appT", [Constructor( "absT", [Var("R2")]) ; Var("X")])],
			    [Application(Var("R2"), Var("X"))]  )  ) ;
			Rule("letStep",
				[Formula("value", [Var("V")], [])],
				Formula("step",
					[Constructor( "let", [Var("V") ; Var("R")])],
					[Application(Var("R"), Var("V"))]  )  ) ;				
		    ])
