open Core.Std
open List

module Digraph : sig
  type 'a t

  val from_adj_lists : ('a * 'a list) list -> 'a t
  val topological_sort : 'a t -> 'a list
end = struct

  type 'a t = ('a, 'a list) Map.Poly.t

  exception Digraph_is_cyclic

  let from_adj_lists adj_lists = Map.Poly.of_alist_exn adj_lists

  let dfs t ~visited ~start =
    let rec traverse curr_path visited node =
      if Set.Poly.mem curr_path node then
        raise Digraph_is_cyclic
      else
        if List.mem visited node then
          visited
        else
          match Map.find t node with
          | None ->
            node :: visited
          | Some neighbors ->
            let new_path = Set.Poly.add curr_path node in
            let visited =
              List.fold neighbors ~init:visited ~f:(traverse new_path)
            in
            node :: visited
    in
    traverse Set.Poly.empty visited start

  let topological_sort t =
    Map.Poly.fold_right t ~init:[] ~f:(fun ~key:node ~data:_ visited ->
      dfs t ~visited ~start:node)
end

let rec is_sorted x = match x with
  | [] -> true
  | h::[] -> true
  | h::h2::t -> if h <= h2 then is_sorted (h2::t) else false;;
  

let topo_compute_order data = List.rev (Digraph.from_adj_lists data |> Digraph.topological_sort)
let topo_test = (topo_compute_order [(1,[]) ; (2,[1])])

