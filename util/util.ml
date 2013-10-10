module L = Batteries.List
module Hashtbl = Batteries.Hashtbl
module Q = Batteries.Queue
module Enum = Batteries.Enum

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration


exception Internal_error of string

let rec label tf internal_signals channels index updates isignals = function
  | And (x,y) -> 
    let lv = (label tf internal_signals channels index updates isignals x)  in
    let rv = (label tf internal_signals channels index updates isignals y) in
    (match (lv,rv) with
    | ("false",_) | (_,"false") -> "false"
    | ("true","true") -> "true"
    | ("true",(_ as s)) | ((_ as s),"true") -> s
    | (_,_) -> lv ^ "&&" ^ rv)
  | Or (x,y) -> 
    let lv = (label tf internal_signals channels index updates isignals x)  in
    let rv = (label tf internal_signals channels index updates isignals y) in
    (match (lv,rv) with
    | ("true",_) | (_,"true") -> "true"
    | ("false","false") -> "false"
    | ("false",(_ as s)) | ((_ as s),"false") -> s
    | (_,_) -> lv ^ "||" ^ rv)
  | Not (Proposition x) as s-> 
    let v = (match x with 
      | Expr x ->
	  if (not (L.exists (fun t -> t = x) isignals)) then
	    if x.[0] = '$' then 
	      let () = output_hum stdout (sexp_of_logic s) in
	      raise (Internal_error "^^^^^^^^^^^^ Not emit proposition impossible!")
	    else 
	      if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) 
	      else x
	  else "false"
      | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!"))
      | Label x -> raise (Internal_error ("Tried to put label " ^ x ^ " on a guard!!"))) in 
    (match v with
    | "false" -> "true"
    | "true" -> "false"
    | _ -> "!"^v)
  | Proposition x as s -> (match x with 
    | Expr x -> 
	if (not (L.exists (fun t -> t = x) isignals)) then
	  if x.[0] = '$' then "true"
	  else 
	  (* This can only ever happen here! *)
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

let get_outgoings o = function
  | ({name=n;incoming=i},guards) ->
    try
      List.iter2 (fun x g -> 
	match Hashtbl.find_option o x with
	| Some ll -> Hashtbl.replace o x ((n,g) :: ll)
	| None -> Hashtbl.add o x [(n,g)]
      ) i guards
    with
    | _ as s -> 
      output_hum stdout (sexp_of_list sexp_of_string i);
      output_hum stdout (sexp_of_list sexp_of_logic guards);
      print_endline ("Node: " ^ n);
      raise s

(* This needs to be fixed. FIXME: just checking in ret is not enough,
   some branches get cutoff unnecessarily! *)
let rec solve q o ret lgn = 
  if not (Q.is_empty q) then
    let element = Q.pop q in
    (* Get all the outgoing nodes from element *)
    (* add these nodes to the queue if they are not already there *)
    let oo = (match Hashtbl.find_option o element.node.name with Some x -> x | None -> []) in
    let (oo,_) = L.split oo in
    (* Check if the oo contains names that are already there in the Q *)
    let oo = L.filter (fun x -> not(Enum.exists (fun y -> y.node.name = x) (Q.enum q))) oo in
    (* Check if these are not already there in ret, because that means they have been visited *)
    let oo = L.filter (fun x -> not(L.exists (fun y -> y.node.name = x) !ret)) oo in
    let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_list sexp_of_string oo); print_endline ""; ELSE () ENDIF in
    (* Add the remaining elements *)
    let oo = L.map (fun x -> L.find (fun y -> y.node.name = x) lgn) oo in
    (* let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_list sexp_of_labeled_graph_node oo); print_endline ""; ELSE () ENDIF in *)
    (* Add to q *)
    let () = List.iter (fun x -> Q.push x q) oo in
    (* Finally add the element to the return list *)
    ret := element :: !ret;
    (* Call it recursively again *)
    solve q o ret lgn
      

(* Reachability using BF traversal *)
let reachability lgn = 
  let ret = ref [] in
  let q = Q.create () in
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> get_outgoings o (x.node,x.guards)) lgn in
  (* Added the starting node *)
  let () = Q.push (L.find (fun {tlabels=t} -> (match t with | Proposition (Label x) -> x = "st" | _ -> false)) lgn) q in
  let () = solve q o ret lgn in
  (* Finally the list is returned *)
  L.sort_unique compare !ret

