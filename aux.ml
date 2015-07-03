
let range a b =
    let rec aux a b =
      if a > b then [] else a :: aux (a+1) b  in
       if a > b then List.rev (aux b a) else aux a b

let getFormalVariables prefix n = if n = 0 then [] else
    let numbers = (range 1 n) in
    let getVars = (fun n -> (prefix^(string_of_int n))) in
    List.map getVars numbers 

let repeat string n =
    let numbers = (range 1 n) in
    let getRepeat = (fun n -> string) in
    List.map getRepeat numbers 

let stringReplace input output =
    Str.global_replace (Str.regexp_string input) output;;

let callAbella command =
  let lines = ref [] in
  let in_channel = Unix.open_process_in command in
  begin
    try
      while true do
        lines := input_line in_channel :: !lines
      done;
    with End_of_file ->
      ignore (Unix.close_process_in in_channel)
  end;
  List.rev !lines
