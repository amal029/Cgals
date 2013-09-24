module L = Batteries.List
module Hashtbl = Batteries.Hashtbl

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration

exception Internal_error of string

let rec label channels index updates isignals = function
  | And (x,y) -> (label channels index updates isignals x) ^ "&&" ^ (label channels index updates isignals y)
  | Or (x,y) -> (label channels index updates isignals x) ^ "||" ^ (label channels index updates isignals y)
  | Not (Proposition x) as s-> "!"^(match x with 
    | Expr x ->
      if (not (L.exists (fun t -> t = x) isignals)) then
	if x.[0] = '$' then 
	  let () = output_hum stdout (sexp_of_logic s) in
	  raise (Internal_error "^^^^^^^^^^^^ Not emit proposition impossible!")
	else if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x
	else "false"
    | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!"))
    | Label x -> raise (Internal_error ("Tried to put label " ^ x ^ " on a guard!!"))) 
  | Proposition x as s -> (match x with 
    | Expr x -> 
      if (not (L.exists (fun t -> t = x) isignals)) then
	if x.[0] = '$' then "true"
	  (* begin updates :=  (Hashtbl.find (L.nth !update_tuple_tbl_ll index) s) :: !updates; "true" end *)
	else 
	  (* (\* This can only ever happen here! *\) *)
	  if not (List.exists (fun (Update t) -> t = x) updates) then
	    if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) 
	    else x
	  else "true"
      else "true"
    | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!"))
    | Label x -> raise (Internal_error ("Tried to put label " ^ x ^ " on a guard!!"))) 
  | True -> "true"
  | False -> "false"
  | _ as s -> 
    let () = output_hum stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non known proposition type when building transition labels" ))


let rec get_updates index = function
  | And(x,y) 
  | Or(x,y) -> (get_updates index x) @ (get_updates index y)
  | Not (Proposition x) | Proposition x as s ->
    (match x with 
    | Expr x -> 
      if x.[0] = '$' then 
	[(Hashtbl.find (L.nth !update_tuple_tbl_ll index) s)]
      else []
    | _ -> [])
  | _ -> []
