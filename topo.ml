let rec searchButReturnVisisted contexts current visited n = 
	if List.mem n visited then visited 
	else if List.mem n current then raise (Failure "Cyclic dependencies") 
    else n :: List.fold_left (searchButReturnVisisted contexts (n :: current)) visited (List.assoc n contexts) 
let deptFirstSearchWithVisited contexts visited n = searchButReturnVisisted contexts [] visited n
let topo_compute_order contexts = let handleByEntry visited entryContext = deptFirstSearchWithVisited contexts visited (fst entryContext) in List.rev (List.fold_left handleByEntry [] contexts)
