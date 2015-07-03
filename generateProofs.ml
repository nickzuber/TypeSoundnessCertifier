
open Type_system
open Aux
open Values
open Nonvalues
open EitherLemma
open CanonicalForms
open Progress
open Preservation 
open Calculi

let main () = (Values.generateValues stlcMin)

if !Sys.interactive then () else main ()
