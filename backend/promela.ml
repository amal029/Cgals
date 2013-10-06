module L = Batteries.List
module Hashtbl = Batteries.Hashtbl
module LL = Batteries.LazyList

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration

exception Internal_error of string

open Pretty

let (++) = append
let (>>) x f = f x

let make_body channels o index signals isignals = function
  (* Make the body of the process!! *)
  | ({name=n},tlabel,_) -> 
    let o = (match Hashtbl.find_option o n with Some x -> x | None -> []) in
    let (o,guards) = L.split o in
    (* First add the location label *)
    ((n ^ "/*" ^ (string_of_logic tlabel) ^ "*/" ^ ":\n") >> text)
    (* ++ List.reduce (++) ( *)
    (*   if o <> [] then *)
    (* 	L.map2 (fun x g -> *)
    (* 	  let updates = Util.get_updates index g in *)
    (* 	  let updates = List.sort_unique compare (List.map (fun (Update x) ->x) updates) in *)
    (* 	  let to_false = ref signals in *)
    (* 	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) updates in *)
    (* 	  L.fold_left (++) empty (L.mapi (fun i x ->  *)
    (* 	    ((if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x) *)
    (* 	     ^ " = false;\t" >> text)) !to_false) *)
    (* 	) o guards  *)
    (*   else [empty] *)
    (* ) *)
    (* Now add the transitions *)
    ++ (L.reduce (++) (
      if o <> [] then
	L.map2 (fun x g ->
	  (* let updates = ref [] in *)
	  let updates = Util.get_updates index g in
	  let g = Util.label channels index updates isignals g in
	  let updates = List.sort_unique compare (List.map (fun (Update x) ->x) updates) in
	  let to_false = ref signals in
	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) updates in
	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) isignals in
	  ("atomic{\n" >> text)
	  ++ L.fold_left (++) empty (L.mapi (fun i x ->
	    ((if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x)
	     ^ " = false;\t" >> text)) !to_false)
	  ++ ("\nif\n" >> text)
	  ++ ((if g <> "" then (":: (" ^ g ^ ") -> ") else (":: true -> ")) >> text)
	  (* These are the updates to be made here!! *)
	  ++ L.fold_left (++) empty (L.mapi (fun i x -> 
	    ((if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x)
	     ^ " = true;\t") >> text) updates)
	  ++ (("goto " ^ x ^ ";\n") >> text)
	  ++ ("fi;\n" >> text)
	  ++ ("}\n" >> text)
	) o guards
      else [("goto " ^ n ^ ";\n">> text)]
    )) 
      
      
let make_process channels o index signals isignals init lgn = 
  (("active proctype CD" ^ (string_of_int index) ^ "(") >> text) 
  (* ++ (L.fold_left (++) empty) (L.mapi (make_args (L.length !ss)) !ss) *)
  ++ ("){\n" >> text)
  ++ (("goto " ^ init ^ ";\n") >> text)
  ++ ((L.reduce (++) (L.map (fun x -> make_body channels o index signals isignals (x.node,x.tlabels,x.guards)) lgn)) >> (4 >> indent))
  ++ ("}\n" >> text)
  ++ (" " >> line)

let make_promela channels signals isignals index init lgn = 
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) lgn in
  group ((make_process channels o index signals isignals init lgn) ++ (" " >> line))
    
