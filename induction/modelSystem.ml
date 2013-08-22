open PropositionalLogic
open TableauBuchiAutomataGeneration
open Sexplib
open Std
open Sexp

module List = Batteries.List
module Hashtbl = Batteries.Hashtbl

exception Internal_error of string

(* The initial hashtbl to hold the mapping from tlabel to node name*)
(* FIXME: Only pause propositions can occur in the tlabel *)
let tbl = Hashtbl.create 100
let replaced = Hashtbl.create 100

let replace = function
  | {node=n} -> n.incoming <- List.map (fun x -> (match (Hashtbl.find_option replaced x) with | None -> x | Some x -> x)) n.incoming
    

let make = function
  | {node=n;tlabels=t} as s -> 
    try
      (* Some node with same tlabel already exists in the hashtbl *)
      let {node=nn} = Hashtbl.find tbl t in
      (* add to replaced *)
      let () = Hashtbl.add replaced n.name nn.name in
      (* replace this current node s with the new_node *)
      nn.incoming <- List.sort_unique compare (nn.incoming @ n.incoming)
    with
    | Not_found -> 
      (* Add to tbl if not there already *)
      Hashtbl.add tbl t s
