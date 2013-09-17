open PropositionalLogic
open TableauBuchiAutomataGeneration
open Sexplib
open Std
open Sexp

module List = Batteries.List
module Array = Batteries.Array
module Hashtbl = Batteries.Hashtbl
module Set = BatSet

exception Internal_error of string

(* The initial hashtbl to hold the mapping from tlabel to node name*)
let tbl = Hashtbl.create 100
let replaced = Hashtbl.create 100
(* let guards = Hashtbl.create 100 *)

let replace = function
  | {node=n} as s -> 
    n.incoming <- List.mapi (fun i x ->
      (match (Hashtbl.find_option replaced x) with 
      | None -> x 
      | Some y -> y)) n.incoming
    

let make = function
  | {node=n;tlabels=t} as s  -> 
    try
      (* Some node with same tlabel already exists in the hashtbl *)
      let ({node=nn;tlabels=tt} as ss) = Hashtbl.find tbl t in
      (* add to replaced *)
      let () = Hashtbl.add replaced n.name nn.name in
      (* replace this current node s with the new_node *)
      let () = nn.incoming <- (nn.incoming @ n.incoming) in
      let () = ss.guards <- (ss.guards @ s.guards) in
      ()
    with
    | Not_found -> 
      (* Add to tbl if not there already *)
      Hashtbl.add tbl t s


let propagate_guards_from_st nodeset = 
  let sts = List.filter (fun {node=n;tlabels=t} -> (match t with 
    | Proposition x -> (match x with Label st -> st="st" | _ -> false) 
    | Not Proposition x ->(match x with Label st -> st="st" | _ -> false)
    | _ -> false)) nodeset in
  let () = List.iter (fun {node=n} ->
    if not (List.for_all (fun x -> x="Init") n.incoming) then
      let () = print_endline n.name in
      raise (Internal_error "modelSystem: proposition st satisfied without an incoming type of Init!!");
  ) sts in
  let () = List.iter (fun ({node=n}as s) -> 
    List.iteri (fun i z ->
      if List.exists(fun {node=st} -> z = st.name) sts then
	begin
	  (* There should only be one in each *)
	  let stg = List.find (fun {node=st} -> z = st.name) sts in
	  if (List.length stg.guards <> 1) then 
	    raise (Internal_error "modelSystem: Length of Init type guards is greater than 1!!");
	  s.guards <- List.mapi (fun y x -> if y = i then solve_logic (And (x, List.hd stg.guards)) else x ) s.guards;
	end
    ) n.incoming
  ) nodeset in 
  List.iter (fun x -> x.guards <- []; x.node.incoming <- []) sts

(* The set functor *)
module PropType = struct
  type t = logic
  let compare = compare
end
module PropSet = Set.Make(PropType)

let find_subformula_equivalents model = function
  | {node=n;tls=llabels;tlabels=labs} as s -> 
    let labels = PropSet.of_enum (List.enum llabels) in
    let new_nodes = List.filter (fun ({node=nn;tls=nllabels}) -> 
      let nlabels = PropSet.of_enum (List.enum nllabels) in
      PropSet.subset labels nlabels) model in 
    (* Now we have all the nodes that need to be replaced!! *)
    (* In place mutable replacement *)
    let new_nodes = List.map (fun {node=n} -> n.name) new_nodes in
    if new_nodes = [] then
      begin
	output_hum stdout (sexp_of_logic labs);
	print_endline ("\nWarning: No replacement for this sub-formula attached to node: " ^ n.name
		       ^ " removing the node form the graph, since it can never happen!");
	let () = List.iter (fun ({node=nn;guards=gg} as sss) ->
	  let indices = List.mapi (fun i x -> if x = n.name then i else -1) nn.incoming in 
	  let left = ref [] in
	  for c = 0 to (List.length sss.guards) - 1 do
	    if not (List.exists (fun x -> x = c) indices) then
	      left := !left @ [List.at sss.guards c];
	  done;
	  sss.guards <- !left;
	  nn.incoming <- List.remove_all nn.incoming n.name;
	) model in ()
      end 
    else
      let () = List.iter (fun ({node=nn} as t) -> 
	let torep = ref [] in
	let gtorep = ref [] in
	let () = List.iter2 (fun x y -> 
	  let glist = List.init (List.length new_nodes) (fun _ -> y) in
	  if x = n.name then
	    (torep := !torep @ new_nodes; gtorep := !gtorep @ glist)
	  else 
	    (torep := !torep @ [x]; gtorep := !gtorep @ [y])
	) nn.incoming t.guards in
	nn.incoming <- !torep;
	t.guards <- !gtorep;
      ) model in
      ()
    
    
