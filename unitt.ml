
open Batteries
open Option
open Aux
open TypedLanguage
open SafeTypedLanguage
open Stlc

let unitType_decl = DeclType("unitType", [])
let unit_decl = DeclTrm("unit", [], [], [])

let unitt = 
Rule("unit",
				[],
		    	Formula("typeOf", [Constructor( "unit", [])], [Constructor( "unitType", [])])) 


let unit_ts = [SpecType(unitType_decl, 
				[SpecTerm(unit_decl, unitt, [])], 
			[])]

let unitt = SafeTypedLanguage(unit_ts, [], None)
let stlc_cbn_unitt = sl_compose stlc_cbn unitt
let stlc_cbv_unitt = sl_compose stlc_cbv unitt
let stlc_par_unitt = sl_compose stlc_par unitt

