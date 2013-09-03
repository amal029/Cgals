(* This file creates the Uppaal timed-automata for model-checking and
   verification from SystemJ program. Notice that this file produces XML
   directly, no pretty-printing is done, because of lack of time. Later
   the xml-light library should be used to produce this automata.

   Author: Avinash Malik 

   Sat Aug 17 10:47:06 NZST 2013

*)
module List = Batteries.List
module Hashtbl = Batteries.Hashtbl
module B = Batteries.Buffer

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration

exception Internal_error of string

let rec label index updates = function
  | And (x,y) -> (label index updates x) ^ "&amp;&amp;" ^ (label index updates y)
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
	begin updates :=  (Hashtbl.find (List.nth !update_tuple_tbl_ll index) s) :: !updates; "true" end
      else x
    | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!")))
  | True -> "true"
  | False -> "false"
  | _ as s -> 
    let () = output_hum stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non And proposition type when building transition labels" ))
(* Make transitions *)
let make_transitions index init ob = function
  | (({name=n;incoming=i}),tlabel,guards) -> 
    let () = IFDEF DEBUG THEN print_endline (string_of_int index) ELSE () ENDIF in
    if i <> [] then
      let () = List.iter2 (fun x g -> 
	let () = B.add_string ob "<transition>\n" in
	let () = B.add_string ob ("<source ref=\"" ^ x ^"\"/>\n") in
	let () = B.add_string ob ("<target ref=\"" ^ n ^ "\"/>\n") in
	(* This is where the labels go! *)
	let updates = ref [] in
	let g = label index updates g in
	let () = (if g <> "" then
	    let () = B.add_string ob "<label kind=\"guard\">" in
	    B.add_string ob g;
	    B.add_string ob "\n</label>\n") in
	let to_false = ref (List.unique (List.of_enum (Hashtbl.values (List.nth !update_tuple_tbl_ll index)))) in
	let () = IFDEF DEBUG THEN print_int index; print_endline "INDEX" ELSE () ENDIF in
	let () = IFDEF DEBUG THEN print_int (List.length !to_false); print_endline "LENGTH" ELSE () ENDIF in
	let () = List.iter (fun x -> to_false := List.filter (fun y -> y <> x) !to_false) !updates in
	let () = B.add_string ob "<label kind=\"assignment\">" in
	let () = List.iteri (fun i (Update x) -> 
	  let () = B.add_string ob (x ^ "=true") in
	  if ((i == (List.length !updates)-1) && (!to_false <> [])) then
	    B.add_string ob ","
	  else if (i < (List.length !updates)-1) then
	    B.add_string ob ","
	) !updates in
	let () = List.iteri (fun i (Update x) -> 
	  let () = B.add_string ob (x ^ "=false") in
	  if i < (List.length !to_false)-1 then 
	    B.add_string ob ", ") !to_false in
	let () = B.add_string ob "</label>\n" in
	let () = B.add_string ob "</transition>\n" in ()) i guards in ()

(* Uppaal locations for the networked automata system*)
let make_locations ob = function
  | ({name=n},tlabel) -> 
    let () = B.add_string ob ("<location id=\"" ^ n ^"\">\n") in
    let () = B.add_string ob ("<name>" ^ (string_of_logic tlabel) ^"</name>\n") in
    let () = B.add_string ob ("<committed/>\n</location>\n") in
    ()

let counter = ref 0
let ss = ref "" 
let ss1 = ref []

(* Outputs the XML file for Uppaal model-checker *)
(* This is for each clock-domain *)
let make_xml signals index init lgn = 
  let ob = B.create(10000) in
  let () = B.add_string ob "<template>\n" in
  counter := !counter + 1;
  let () = B.add_string ob ("<name>Template" ^ (string_of_int !counter) ^"</name>\n") in
  (* Add all the boolean signal declarations!! *)
  if signals <> [] then
    begin
      let () = Buffer.add_string ob "<declaration>" in
      let () = Buffer.add_string ob "bool " in
      let () = List.iteri(fun i x -> 
	let () = Buffer.add_string ob x in
	if i = ((List.length signals)-1) then
	  Buffer.add_string ob ";\n"
	else
	  Buffer.add_string ob ", "
      ) signals in
      let () = Buffer.add_string ob "</declaration>\n" in
      ()
    end;
  ss := !ss ^ "Process" ^ (string_of_int !counter) ^ " = Template" ^ (string_of_int !counter) ^ "();\n";
  ss1 := ("Process" ^ (string_of_int !counter)) :: !ss1;
  (* make the nodes *)
  let () = List.iter (make_locations ob) (List.map (fun x -> (x.node,x.tlabels)) lgn) in
  let () = B.add_string ob ("<init ref=\"" ^ init ^ "\"/>\n") in
  (* Make transitions *)
  let () = List.iter (make_transitions index init ob) (List.map (fun x -> (x.node,x.tlabels,x.guards)) lgn) in
  (* Add the system declaration *)
  let () = B.add_string ob "</template>\n" in 
  ob

let make_uppaal strings = 
  let ob = B.create(10000) in
  (* Start the automata *)
  let () = B.add_string ob "<nta>\n" in
  let () = B.add_string ob "<declaration>//Global declarations\n</declaration>\n" in
  let () = B.add_buffer ob strings in
  let () = B.add_string ob "<system>\n" in
  let () = B.add_string ob !ss in
  let () = B.add_string ob "system " in
  let () = List.iteri(fun i x -> 
    let () = Buffer.add_string ob x in
    if i = ((List.length !ss1)-1) then
      Buffer.add_string ob ";\n"
    else
      Buffer.add_string ob ", "
  ) (List.rev !ss1) in
  let () = B.add_string ob "</system>\n" in
  let () = B.add_string ob "</nta>" in ob
