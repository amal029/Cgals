open PropositionalLogic
open TableauBuchiAutomataGeneration
open Sexplib
open Std
open Sexp

module List = Batteries.List
module Array = Batteries.Array
module Hashtbl = Batteries.Hashtbl

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
