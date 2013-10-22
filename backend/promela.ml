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
let (|>) x f = f x

let make_body asignals internal_signals channels o index signals isignals = function
  (* Make the body of the process!! *)
  | ({name=n},tlabel,_) -> 
    let o = (match Hashtbl.find_option o n with Some x -> x | None -> []) in
    let (o,guards) = L.split o in
    (* First add the location label *)
    ((n ^ "/*" ^ (string_of_logic tlabel) ^ "*/" ^ ":\n") >> text)
    (* Now add the transitions *)
    ++ ("atomic {\n" >> text)
    ++ ("\nif\n" >> text)
    ++ (L.reduce (++) (
      if o <> [] then
	L.map2 (fun x g ->
	  (* let updates = ref [] in *)
	  let updates = Util.get_updates index g in
	  let datastmts = (L.filter (fun x -> (match x with | DataUpdate _ ->true | _ -> false)) updates) in
	  let updates1 = L.sort_unique compare ((L.map 
						   (fun x -> (match x with | Update x ->x | _ ->  raise (Internal_error "Cannot happen!!"))))
						   (L.filter (fun x -> (match x with | Update _ ->true | _ -> false)) updates)) in
	  let to_false = ref signals in
	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) updates1 in
	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) isignals in
	  let g = Util.label "promela" !to_false internal_signals channels index updates isignals asignals g in
	  let updates = updates1 in
	  let asignals_names = List.split asignals |> (fun (x,_) -> x) in
	  let asignals_options = List.split asignals |> (fun (_,y) -> y) in
	  if g <> "false" then
	    (* ("atomic{\n" >> text) *)
	    ((if g <> "" then (":: (" ^ g ^ ") -> ") else (":: true -> ")) >> text)
	    (* These are the updates to be made here!! *)
	    ++ L.fold_left (++) empty (L.mapi (fun i x -> 
	      ((if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x)
	       ^ " = true;\n") >> text) updates)
	    ++ L.fold_left (++) empty (L.mapi (fun i x ->
	      ((if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x)
	       ^ " = false;\n" >> text)) !to_false)
	    (* Add the data stmts *)
	    ++ ((L.fold_left (^) "" (L.map (Util.build_data_stmt asignals index "promela") datastmts)) >> text)
	    ++ L.fold_left (++) empty (Util.map2i (fun i x y -> 
	      (match y with
	      | None -> Pretty.empty
	      | Some r -> 
		("CD"^(string_of_int index)^"_"^x^"_val_pre = CD" ^ (string_of_int index)^"_"^x^"_val;\n" >> Pretty.text)
		++ ("CD"^(string_of_int index)^"_"^x^"_val = "^r.Systemj.v^";\n"  >> Pretty.text)
	      ))asignals_names asignals_options)
	    ++ (("goto " ^ x ^ ";\n") >> text)
	  else empty
	) o guards
      else [(":: goto " ^ n ^ ";\n">> text)]
    )) 
    ++ ("fi;\n" >> text)
    ++ ("}\n" >> text)
      
      
let make_process internal_signals channels o index signals isignals init asignals lgn =
  (("active proctype CD" ^ (string_of_int index) ^ "(") >> text)
  ++ ("){\n" >> text)
  ++ (("goto " ^ init ^ ";\n") >> text)
  ++ ((L.reduce (++) (L.map (fun x -> make_body asignals internal_signals channels o index signals isignals (x.node,x.tlabels,x.guards)) lgn))
	 |> (4 |> indent))
  ++ ("}\n" >> text)
  ++ (" " >> line)

let make_promela channels internal_signals signals isignals index init asignals lgn = 
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) lgn in
  group ((make_process internal_signals channels o index signals isignals init asignals lgn) ++ (" " >> line))
    
