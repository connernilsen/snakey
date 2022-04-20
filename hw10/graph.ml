open Printf

module NeighborSet = Set.Make (String)

type neighborst = NeighborSet.t

module Graph = Map.Make (String)

type grapht = neighborst Graph.t

module StringSet = Set.Make(String)

type livet = StringSet.t

let empty : grapht = Graph.empty

let add_node (g : grapht) (name : string) : grapht =
  if Graph.mem name g then g else Graph.add name NeighborSet.empty g
;;

let add_directed_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_node (add_node g n1) n2 in
  let curr_neighbors = Graph.find n1 g' in
  Graph.add n1 (NeighborSet.add n2 curr_neighbors) g'
;;

let add_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_directed_edge g n1 n2 in
  add_directed_edge g' n2 n1
;;

let connect_with_rest (g : grapht) (nodes : StringSet.t) (node : string) : grapht =
  StringSet.fold
    (fun (subitem : string) (acc : grapht) -> 
       if subitem = node 
       then acc 
       else add_edge acc node subitem)
    nodes
    g
;;

let connect_all (g : grapht) (nodes : StringSet.t) : grapht =
  StringSet.fold
    (fun (item : string) (acc : grapht) -> 
       let acc = add_node acc item in
       connect_with_rest acc nodes item
    ) nodes g
;;

let graph_union (g1 : grapht) (g2 : grapht) : grapht =
  Graph.fold (fun (from : string) (to_ss : neighborst) (acc : grapht) -> 
      match Graph.find_opt from acc with 
      | None -> Graph.add from to_ss acc
      | Some(neighbors) -> 
        Graph.add from (NeighborSet.union to_ss neighbors) acc)
    g2
    g1
;;

let get_neighbors (g : grapht) (name : string) : string list =
  if Graph.mem name g
  then NeighborSet.fold (fun n ns -> n :: ns) (Graph.find name g) []
  else []
;;

let get_vertices (g : grapht) : string list =
  let keys, _ = List.split (Graph.bindings g) in keys
;;

let string_of_stringset (s : StringSet.t) : string =
  let elems = StringSet.elements s in 
  ExtString.String.join ", " elems
;;

let string_of_graph (g: grapht): string =
  let string_of_neighbors (n: string): string =
    ExtString.String.join ", " (get_neighbors g n)
  in
  ExtString.String.join "\n" (List.map (fun k -> sprintf "%s: %s" k (string_of_neighbors k)) (get_vertices g))
;;
