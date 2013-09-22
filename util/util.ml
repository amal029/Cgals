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
	if x.[0] = '$' then 
	  begin updates :=  (Hashtbl.find (L.nth !update_tuple_tbl_ll index) s) :: !updates; "true" end
	else if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x
      else "true"
    | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!"))
    | Label x -> raise (Internal_error ("Tried to put label " ^ x ^ " on a guard!!"))) 
  | True -> "true"
  | False -> "false"
  | _ as s -> 
    let () = output_hum stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non known proposition type when building transition labels" ))

