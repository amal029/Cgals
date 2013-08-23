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
let guards = Hashtbl.create 100

let replace = function
  | {node=n} as s -> 
    n.incoming <- List.mapi (fun i x ->
      (match (Hashtbl.find_option replaced x) with 
      | None -> x 
      | Some y -> 
	let a = Array.of_list s.guards in
	let () = a.(i) <- Hashtbl.find guards x in
	s.guards <- Array.to_list a;
	y)) n.incoming
    

let make = function
  | {node=n;tlabels=t} as s  -> 
    try
      (* Some node with same tlabel already exists in the hashtbl *)
      let ({node=nn;tlabels=tt} as ss) = Hashtbl.find tbl t in
      (* add to replaced *)
      let () = Hashtbl.add replaced n.name nn.name in
      (* replace this current node s with the new_node *)
      let () = nn.incoming <- (nn.incoming @ n.incoming) in
      let () = ss.guards <- (ss.guards @ (Array.to_list (Array.create (List.length s.guards) True))) in
      let () = Hashtbl.add guards n.name (solve_logic (List.reduce (fun x y -> And(x,y)) s.guards )) in
      ()
    with
    | Not_found -> 
      (* Add to tbl if not there already *)
      Hashtbl.add tbl t s

