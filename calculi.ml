
open Type_system

let emptyTS = TypeSystem([], [], [])


let stlcWithBool = TypeSystem(
			  [DeclType("arrow", "typ", ["abs"], ["app"], [Simple("typ") ; Simple("typ")]) ;
			   DeclType("bool", "typ", ["tt" ; "ff"], ["if"], []) ;
				    ],
	    [  DeclTrm("abs", "term", Contextual [], [Abstraction("term", "term")]);
		    DeclTrm("tt", "term", Contextual [], []);
		    DeclTrm("ff", "term", Contextual [], []);
		    DeclTrm("app", "term", Contextual [1;2], [Simple("term"); Simple("term")]) ;
		    DeclTrm("if", "term", Contextual [1;2;3], [Simple("term") ; Simple("term") ; Simple("term")]);
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
		    [Formula("typeOf",     [Var("E1")],
			     [Constructor( "arrow", [Var("T1") ;
					             Var("T2")]  )  ]  ) ;
		    Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf",
			    [Constructor( "app", [Var("E1") ;
					          Var("E2")])],
			    [Var("T2")]  )  ) ;
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
		    [],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("APPLIED")])],
			    [Application(Var("R"), Var("APPLIED"))]  )  ) ;

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


let stlcPairs = TypeSystem(
			  [DeclType("arrow", "typ", ["abs"], ["app"], [Simple("typ") ; Simple("typ")]) ;
		   		DeclType("bool", "typ", ["tt" ; "ff"], ["if"], []) ;
			   	DeclType("times", "typ", ["pair"], ["fst" ; "snd"], [Simple("typ") ; Simple("typ")]) ;
				    ],
	    [  DeclTrm("abs", "term", Contextual [], [Abstraction("term", "term")]);
		    DeclTrm("tt", "term", Contextual [], []);
		    DeclTrm("ff", "term", Contextual [], []);
		    DeclTrm("pair", "term", Contextual [1;2], [Simple("term"); Simple("term")]);
		    DeclTrm("app", "term", Contextual [1;2], [Simple("term"); Simple("term")]) ;
		    DeclTrm("if", "term", Contextual [1;2;3], [Simple("term") ; Simple("term") ; Simple("term")]);
			DeclTrm("fst", "term", Contextual [1], [Simple("term")]);
			DeclTrm("snd", "term", Contextual [1], [Simple("term")]);
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
   	       Rule("pair",
   	          [Formula("typeOf", [Var("E1")] ,  [Var("T1")]) ;
			  Formula("typeOf", [Var("E2")] ,  [Var("T2")])
			  ],
   	          Formula("typeOf",     [Constructor( "pair", [Var("E1") ; Var("E2")])],      [Constructor( "times", [Var("T1") ; Var("T2")])])) ;
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
  	       Rule("fst",
  	          [Formula("typeOf", [Var("E")] ,  [Constructor( "times", [Var("T1") ; Var("T2")])])],
  	          Formula("typeOf",     [Constructor( "fst", [Var("E")])],      [Var("T1")])) ;
	       Rule("snd",
	          [Formula("typeOf", [Var("E")] ,  [Constructor( "times", [Var("T1") ; Var("T2")])])],
	          Formula("typeOf",     [Constructor( "snd", [Var("E")])],      [Var("T2")])) ;
	       Rule("beta",
		    [],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("APPLIED")])],
			    [Application(Var("R"), Var("APPLIED"))]  )  ) ;

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
 	       Rule("fst",
 		    [],
 		    Formula("step",
 			    [Constructor( "fst", [Constructor( "pair", [Var("E1") ; Var("E2")])])],
 			    [Var("E1")]  )  ) ;
  	       Rule("snd",
  		    [],
  		    Formula("step",
  			    [Constructor( "snd", [Constructor( "pair", [Var("E1") ; Var("E2")])])],
  			    [Var("E2")]  )  ) ;
		    ])


let stlcFix = TypeSystem(
			  [DeclType("arrow", "typ", ["abs"], ["app" ; "fix"], [Simple("typ") ; Simple("typ")]) ;
			   DeclType("bool", "typ", ["tt" ; "ff"], ["if"], []) ;
				    ],
	    [  DeclTrm("abs", "term", Contextual [], [Abstraction("term", "term")]);
		    DeclTrm("tt", "term", Contextual [], []);
		    DeclTrm("ff", "term", Contextual [], []);
		    DeclTrm("app", "term", Contextual [1;2], [Simple("term"); Simple("term")]) ;
		    DeclTrm("if", "term", Contextual [1;2;3], [Simple("term") ; Simple("term") ; Simple("term")]);
		    DeclTrm("fix", "term", Contextual [], [Abstraction("term", "term")]);
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
		    [Formula("typeOf",     [Var("E1")],
			     [Constructor( "arrow", [Var("T1") ;
					             Var("T2")]  )  ]  ) ;
		    Formula("typeOf", [Var("E2")] ,  [Var("T1")])
		    ],
		    Formula("typeOf",
			    [Constructor( "app", [Var("E1") ;
					          Var("E2")])],
			    [Var("T2")]  )  ) ;
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
	       Rule("fix",
	          [Hypothetical(Var("T"), Application(Var("R"), Var("x")), Var("T"))],
		    Formula("typeOf",
			    [Constructor( "fix", [Var("R")])] ,
			    [Var("T")]  )  ) ;

	       Rule("beta",
		    [],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("APPLIED")])],
			    [Application(Var("R"), Var("APPLIED"))]  )  ) ;

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
	       Rule("fix",
		    [],
		    Formula("step",
			    [Constructor( "fix", [Var("R")])],
			    [Application(Var("R"), Constructor( "fix", [Var("R")]))]  )  ) 
		    ])


let systemF_CBN = TypeSystem(
			  [DeclType("arrow", "typ", ["abs"], ["app"], [Simple("typ") ; Simple("typ")]) ;
			   DeclType("bool", "typ", ["tt" ; "ff"], ["if"], []) ;
			   DeclType("all", "typ", ["absT"], ["appT"], [Abstraction("typ", "typ")]) ;
				    ],
	    [  DeclTrm("abs", "term", Contextual [], [Abstraction("term", "term")]);
		    DeclTrm("tt", "term", Contextual [], []);
		    DeclTrm("ff", "term", Contextual [], []);
		    DeclTrm("absT", "term", Contextual [], [Abstraction("typ", "term")]) ;
		    DeclTrm("app", "term", Contextual [1], [Simple("term"); Simple("term")]) ;
		    DeclTrm("if", "term", Contextual [1;2;3], [Simple("term") ; Simple("term") ; Simple("term")]);
		    DeclTrm("appT", "term", Contextual [1], [Simple("term"); Simple("typ")]) ;
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
	       Rule("appT",
		    [Formula("typeOf",     [Var("E")],
			     [Constructor("all", [Var("R")])]) 
		    ],
		    Formula("typeOf",
			    [Constructor( "appT", [Var("E") ;
					          Var("X")])],
			    [Application(Var("R"),Var("X"))]  )  ) ;
	       Rule("beta",
		    [],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("APPLIED")])],
			    [Application(Var("R"), Var("APPLIED"))]  )  ) ;

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
	       Rule("betaT",
		    [],
		    Formula("step",
			    [Constructor( "appT", [Constructor( "absT", [Var("R2")]) ; Var("X")])],
			    [Application(Var("R2"), Var("X"))]  )  ) 
		    ])
			
let systemF_CBV = TypeSystem(
			  [DeclType("arrow", "typ", ["abs"], ["app"], [Simple("typ") ; Simple("typ")]) ;
			   DeclType("bool", "typ", ["tt" ; "ff"], ["if"], []) ;
			   DeclType("all", "typ", ["absT"], ["appT"], [Abstraction("typ", "typ")]) ;
				    ],
	    [  DeclTrm("abs", "term", Contextual [], [Abstraction("term", "term")]);
		    DeclTrm("tt", "term", Contextual [], []);
		    DeclTrm("ff", "term", Contextual [], []);
		    DeclTrm("absT", "term", Contextual [], [Abstraction("typ", "term")]) ;
		    DeclTrm("app", "term", Sequential, [Simple("term"); Simple("term")]) ;
		    DeclTrm("if", "term", Contextual [1;2;3], [Simple("term") ; Simple("term") ; Simple("term")]);
		    DeclTrm("appT", "term", Contextual [1], [Simple("term"); Simple("typ")]) ;
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
	       Rule("appT",
		    [Formula("typeOf",     [Var("E")],
			     [Constructor("all", [Var("R")])]) 
		    ],
		    Formula("typeOf",
			    [Constructor( "appT", [Var("E") ;
					          Var("X")])],
			    [Application(Var("R"),Var("X"))]  )  ) ;
	       Rule("beta",
		    [Formula("value", [Var("APPLIED")], [])],
		    Formula("step",
			    [Constructor( "app", [Constructor( "abs", [Var("R")]) ; Var("APPLIED")])],
			    [Application(Var("R"), Var("APPLIED"))]  )  ) ;

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
	       Rule("betaT",
		    [],
		    Formula("step",
			    [Constructor( "appT", [Constructor( "absT", [Var("R2")]) ; Var("X")])],
			    [Application(Var("R2"), Var("X"))]  )  ) 
		    ])

