
open Batteries
open Type_system
open Aux

let toErrorPremise term = Formula("error", [term], [])

let generateErrors ts = match ts with TypeSystem(signatureTypes,signatureTerms,rules) -> 
	let toErrorDefinitions termDecl = (let (canonical, vars) = (canonicalForTerm termDecl) in Rule("error", [], toErrorPremise canonical)) in 
	 Type_system.extend ts (List.map toErrorDefinitions (getErrors signatureTerms))

