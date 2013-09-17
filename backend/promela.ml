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
  ++ ((if index = (length-1) then "" else "; ") >> text)

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
	begin updates :=  (Hashtbl.find (L.nth !update_tuple_tbl_ll index) s) :: !updates; "true" end
      else x
    | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!")))
  | True -> "true"
  | False -> "false"
  | _ as s -> 
    let () = output_hum stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non And proposition type when building transition labels" ))

let make_body o index signals = function
  (* Make the body of the process!! *)
  | ({name=n},tlabel,_) -> 
    let o = (match Hashtbl.find_option o n with Some x -> x | None -> []) in
    let (o,guards) = L.split o in
    (* First add the location label *)
    ((n ^ "/*" ^ (string_of_logic tlabel) ^ "*/" ^ ":\n") >> text)
    ++ ("if\n" >> text)
    (* Now add the transitions *)
    ++ (L.reduce (++) (
      if o <> [] then
	L.map2 (fun x g ->
	  let updates = ref [] in
	  let g = label index updates g in
	  let updates = List.unique (List.map (fun (Update x) ->x) !updates) in
	  let to_false = ref signals in
	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) updates in
	  ((if g <> "" then (":: (" ^ g ^ ") -> ") else (":: true -> ")) >> text)
	  (* These are the updates to be made here!! *)
	  ++ L.fold_left (++) empty (L.mapi (fun i x -> ((x ^ "=true;\t") >> text)) updates)
	  ++ L.fold_left (++) empty (L.mapi (fun i x -> ((x ^ "=false;\t") >> text)) !to_false)
	  ++ (("goto " ^ x ^ ";\n") >> text)
	) o guards
      else [("::skip;\n" >> text)]
    )) 
    ++ ("fi;\n" >> text)
      
      
let make_process o index signals init lgn = 
  (("active proctype CD" ^ (string_of_int index) ^ "(") >> text) 
  ++ (L.fold_left (++) empty) (L.mapi (make_args (L.length signals)) signals)
  ++ ("){\n" >> text)
  ++ (("goto " ^ init ^ ";\n") >> text)
  ++ ((L.reduce (++) (L.map (fun x -> make_body o index signals (x.node,x.tlabels,x.guards)) lgn)) >> (4 >> indent))
  ++ ("}\n" >> text)
  ++ (" " >> line)

let make_promela signals index init lgn = 
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> get_outgoings o (x.node,x.guards)) lgn in
  group ((make_process o index signals init lgn) ++ (" " >> line))
    
