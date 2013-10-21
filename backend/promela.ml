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

let make_body ff internal_signals channels o index signals isignals = function
  (* Make the body of the process!! *)
  | ({name=n},tlabel,_) -> 
    let o = (match Hashtbl.find_option o n with Some x -> x | None -> []) in
    let (o,guards) = L.split o in
    (* First add the location label *)
    let ret1 = 
      ((n ^ "/*" ^ (string_of_logic tlabel) ^ "*/" ^ ":\n") >> text)
      ++ ("atomic {\n" >> text)
      (* Now add the transitions *)
      ++ (L.reduce (++) (
	if o <> [] then
	  L.map2 (fun x g ->
	    (* let updates = ref [] in *)
	    let updates = Util.get_updates index g in
	    let updates1 = List.sort_unique compare (List.map (fun (Update x) ->x) updates) in
	    let to_false = ref signals in
	    let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) updates1 in
	    let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) isignals in
	    let g = Util.label !to_false internal_signals channels index updates isignals g in
	    let updates = updates1 in
	    if g <> "false" then
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
	      ++ ((":: else skip;\n") >> text)
	      ++ ("fi;\n" >> text)
	      ++ ("}\n" >> text)
	    else begin ff := x::!ff; empty end
	  ) o guards
	else [("  goto " ^ n ^ ";\n">> text)]
      (* else [(" skip;\n">> text)] *)
      )) 
      ++ ("}\n" >> text) in
    (n,ret1)
	
      
let make_process internal_signals channels o index signals isignals init lgn = 
  let ff = ref [] in 
  let bodies = (L.map (fun x -> make_body ff internal_signals channels o index signals isignals (x.node,x.tlabels,x.guards)) lgn) in
  (* Remove all the bodies that are in the ff list *)
  let ff = List.sort_unique compare !ff in
  let () = IFDEF DEBUG THEN print_endline "removing nodes: " ELSE () ENDIF in
  let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_list sexp_of_string ff) ELSE () ENDIF in
  let (_,bodies) = List.filter (fun(x,y) -> not (List.exists (fun t -> t = x) ff)) bodies >> List.split in
  let lgn = Util.reachability ff lgn in
  let rr = 
    (("active proctype CD" ^ (string_of_int index) ^ "(") >> text)
    (* ++ (L.fold_left (++) empty) (L.mapi (make_args (L.length !ss)) !ss) *)
    ++ ("){\n" >> text)
    ++ (("goto " ^ init ^ ";\n") >> text)
    ++ ((L.reduce (++) bodies) >> (4 >> indent))
    ++ ("}\n" >> text)
    ++ (" " >> line) in
  (rr,lgn)

let make_promela channels internal_signals signals isignals index init lgn = 
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) lgn in
  let (rr,lgn) = make_process internal_signals channels o index signals isignals init lgn in
  (group (rr ++ (" " >> line)),lgn)
    
