module L = Batteries.List
module Hashtbl = Batteries.Hashtbl

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration

exception Internal_error of string

open Pretty

let (++) = append
let (>>) x f = f x

let make_args length index signal = 
  (("bool " ^ signal) >> text)
  ++ ((if index = (length-1) then "" else ", ") >> text)

let get_outgoings o = function
  | ({name=n;incoming=i},guards) ->
    List.iter2 (fun x g -> 
      let () = IFDEF DEBUG THEN print_endline x ELSE () ENDIF in
      match Hashtbl.find_option o x with
      | Some ll -> Hashtbl.replace o x ((n,g) :: ll)
      | None -> Hashtbl.add o x [(n,g)]
    ) i guards

let rec label index updates = function
  | And (x,y) -> (label index updates x) ^ "&&" ^ (label index updates y)
  | Or (x,y) -> (label index updates x) ^ "||" ^ (label index updates y)
  | Not (Proposition x) as s-> "!"^(match x with 
    | Label x -> x 
    | Expr x ->
      if x.[0] = '$' then 
	let () = output_hum stdout (sexp_of_logic s) in
	raise (Internal_error "^^^^^^^^^^^^ Not emit proposition impossible!")
      else x
    | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!")))
  | Proposition x as s -> (match x with 
    | Label x -> x 
    | Expr x -> 
      if x.[0] = '$' then 
	let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_logic s) ELSE () ENDIF in
	let () = IFDEF DEBUG THEN print_endline (string_of_int index) ELSE () ENDIF in
	let () = IFDEF DEBUG THEN print_endline (string_of_int (L.length !update_tuple_tbl_ll)) ELSE () ENDIF in
	begin updates :=  (Hashtbl.find (L.nth !update_tuple_tbl_ll index) s) :: !updates; "true" end
      else x
    | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!")))
  | True -> "true"
  | False -> "false"
  | _ as s -> 
    let () = output_hum stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non And proposition type when building transition labels" ))

let make_body o index = function
  (* Make the body of the process!! *)
  | ({name=n},tlabel,_) -> 
    let o = (match Hashtbl.find_option o n with Some x -> x | None -> []) in
    let (o,guards) = L.split o in
    let () = IFDEF DEBUG THEN print_endline (string_of_bool (L.length o = L.length guards)) ELSE () ENDIF in
    (* First add the location label *)
    ((n ^ ":\n") >> text)
    (* Now add the transitions *)
    ++ (indent 4 (L.reduce (++) (
      if o <> [] then
	L.map2 (fun x g ->
	  let updates = ref [] in
	  let g = label index updates g in
	  let () = IFDEF DEBUG THEN print_endline "getting to_false list" ELSE () ENDIF in
	  let to_false = ref (L.unique (L.of_enum (Hashtbl.values (L.nth !update_tuple_tbl_ll index)))) in
	  let () = IFDEF DEBUG THEN print_endline (string_of_int (L.length !to_false)) ELSE () ENDIF in
	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) !updates in
	  ("if\n" >> text)
	  ++ ((if g <> "" then (":: (" ^ g ^ ") -> ") else (":: true -> ")) >> text)
	  (* These are the updates to be made here!! *)
	  ++ L.fold_left (++) empty (L.mapi (fun i (Update x) -> ((x ^ "=true;\t") >> text)) !updates)
	  ++ L.fold_left (++) empty (L.mapi (fun i (Update x) -> ((x ^ "=false;\t") >> text)) !to_false)
	  ++ (("goto " ^ x ^ ";\n") >> text)
	  ++ ("fi;\n" >> text)
	) o guards
      else [("skip;\n" >> text)]
    ))) 
      
      
let make_process o index signals lgn = 
  (("active proctype CD" ^ (string_of_int index) ^ "(") >> text) 
  ++ (L.reduce (++)) (L.mapi (make_args (L.length signals)) signals)
  ++ ("){\n" >> text)
  ++ (" " >> line)
  ++ ((L.reduce (++) (L.map (fun x -> make_body o index (x.node,x.tlabels,x.guards)) lgn)) >> (4 >> indent))
  ++ ("}\n" >> text)
  ++ (" " >> line)

let make_promela signals index init lgn = 
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> get_outgoings o (x.node,x.guards)) lgn in
  group ((make_process o index signals lgn) ++ (" " >> line))
    
