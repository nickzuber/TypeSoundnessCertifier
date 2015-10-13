
let range a b =
    let rec aux a b =
      if a > b then [] else a :: aux (a+1) b  in
       if a > b then List.rev (aux b a) else aux a b

let getFormalVariables prefix n = if n = 0 then [] else
    let numbers = (range 1 n) in
    let getVars = (fun n -> (prefix^(string_of_int n))) in
    List.map getVars numbers 

let repeat obj n = if n = 0 then [] else 
    let numbers = (range 1 n) in
    let getRepeat = (fun n -> obj) in
    List.map getRepeat numbers 

let nthMinusOne myList n = 
	List.nth myList (n-1) 

let stringReplace input output =
    Str.global_replace (Str.regexp_string input) output;;

let find obj myList = 
	let getIndex = fun obj1 -> fun index -> fun obj2 -> if obj1 = obj2 then index+1 else 0 in 
		List.fold_left max 0 (List.mapi (getIndex obj) myList)
	
let decrement n = n-1

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
  
let withSpaces = String.concat " "

