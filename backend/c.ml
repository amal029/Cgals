
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

let make_body asignals internal_signals channels o index signals isignals = function
  (* Make the body of the process!! *)
  | ({name=n},tlabel,_) -> 
    let o = (match Hashtbl.find_option o n with Some x -> x | None -> []) in
    let (o,guards) = L.split o in
    (* First add the location label *)
    ((n ^ "/*" ^ (string_of_logic tlabel) ^ "*/" ^ ":\n") >> text)
    (* Now add the transitions *)
    ++ (L.reduce (++) (
      if o <> [] then
	L.map2 (fun x g ->
	  (* let updates = ref [] in *)
	  let updates = Util.get_updates index g in
	  (* let updates1 = List.sort_unique compare (List.map (fun (Update x) ->x) updates) in *)
	  let datastmts = (L.filter (fun x -> (match x with | DataUpdate _ ->true | _ -> false)) updates) in
	  let updates1 = List.sort_unique compare ((List.map 
						      (fun x -> (match x with | Update x ->x | _ ->  raise (Internal_error "Cannot happen!!"))))
						      (List.filter (fun x -> (match x with | Update _ ->true | _ -> false)) updates)) in
	  let to_false = ref signals in
	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) updates1 in
	  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) isignals in
	  let g = Util.label "c" !to_false internal_signals channels index updates [] asignals g in
	  let updates = updates1 in
	  let asignals_names = List.split asignals |> (fun (x,_) -> x) in
	  let asignals_options = List.split asignals |> (fun (_,y) -> y) in
	  if g <> "false" then
	    ("\nif" >> text)
	    ++ ((if g <> "" then ("(" ^ g ^ ") {\n") else "") >> text)
	    (* These are the updates to be made here!! *)
	    ++ L.fold_left (++) empty (L.mapi (fun i x -> 
	      ((if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x)
	       ^ " = true;\n printf(\"Emitted: "^x^"\\n\");\n") >> text) updates)
	    ++ ((L.fold_left (^) "" (L.map (Util.build_data_stmt asignals index "c") datastmts)) >> text)
	    ++ L.fold_left (++) empty (Util.map2i (fun i x y -> 
	      (match y with
	      | None -> Pretty.empty
	      | Some r -> 
		("CD"^(string_of_int i)^"_"^x^"_val_pre = CD" ^ (string_of_int i)^"_"^x^"_val;\n" >> Pretty.text)
		++ ("CD"^(string_of_int i)^"_"^x^"_val = "^r.Systemj.v^";\n"  >> Pretty.text)
	      ))asignals_names asignals_options)
	    ++ L.fold_left (++) empty (L.mapi (fun i x ->
	      ((if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) else x)
	       ^ " = false;\n" >> text)) !to_false)
	    ++ (("goto " ^ x ^ ";\n") >> text)
	    ++ ("}\n" >> text)
	  else empty
	) o guards
      else [("goto " ^ n ^ ";\n">> text)]
    )) 

let make_process internal_signals channels o index signals isignals init asignals lgn = 
  (("void CD" ^ (string_of_int index) ^ "(") >> text) 
  (* ++ (L.fold_left (++) empty) (L.mapi (make_args (L.length !ss)) !ss) *)
  ++ ("){\n" >> text)
  ++ (("goto " ^ init ^ ";\n") >> text)
  ++ ((L.reduce (++) (L.map (fun x -> make_body asignals internal_signals channels o index signals isignals (x.node,x.tlabels,x.guards)) lgn)) >> (4 >> indent))
  ++ ("}\n" >> text)
  ++ (" " >> line)

let make_main index = 
  ("int main(){\n" >> text) ++
    ("while(true){\n" >> text) ++ 
    L.fold_left (++) empty (L.init index (fun x -> "CD"^(string_of_int x)^"();\n" >> text))
  ++ ("}\n" >> text) 
  ++("}\n" >> text)

let make_c channels internal_signals signals isignals index init asignals lgn = 
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) lgn in
  group ((make_process internal_signals channels o index signals isignals init asignals lgn) ++ (" " >> line))
    
