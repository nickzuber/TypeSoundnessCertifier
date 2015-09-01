
open Type_system
open Aux

let toValuePremises var = Formula("value", [var], [])

let toValueDefs_byTermDecl signatureEntry = match signatureEntry with DeclTrm(c,kind, ctx, arguments) ->
                            let (terms, abstractions, theRest) = getTermsAndTheRest arguments in 
							let howmany = (match ctx with 
							| Sequential -> Aux.range 0 ((List.length terms) - 1)
							| Contextual(args) -> List.map Aux.decrement args) in 
							let valArguments = (List.map (List.nth terms) howmany) in
                            Rule("value_"^c, (List.map toValuePremises valArguments), Formula("value", [Constructor(c, terms @ abstractions @ theRest)], []))

let rec findDeclOfConstructors signatureTerms constructor = match signatureTerms with DeclTrm(c, kind, ctx, arguments)::rest -> if c = constructor then DeclTrm(c,kind,ctx,arguments) else findDeclOfConstructors rest constructor

let toValueDefs_byDecl signatureTerms decl = match decl with 
   | DeclType(c,kind,constructors,deconstructors,arguments) -> List.map toValueDefs_byTermDecl (List.map (findDeclOfConstructors signatureTerms) constructors)

let toValueDefs ts =  match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> List.concat (List.map (toValueDefs_byDecl signatureTerms) signatureTypes)

let generateValues ts = Type_system.extend ts (toValueDefs ts)


