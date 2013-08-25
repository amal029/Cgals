(* This file creates the Uppaal timed-automata for model-checking and
   verification from SystemJ program. Notice that this file produces XML
   directly, no pretty-printing is done, because of lack of time. Later
   the xml-light library should be used to produce this automata.

   Author: Avinash Malik 

   Sat Aug 17 10:47:06 NZST 2013

*)
module List = Batteries.List
module B = Batteries.Buffer

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration

exception Internal_error of string

(* let decls = ref [] *)

let rec label = function
  | And (x,y) -> (label x) ^ "&amp;&amp;" ^ (label y)
  | Not (Proposition x) -> "!"^(match x with | Label x -> x | Expr x -> x | Update x -> x^"=true")
  | Proposition x -> (match x with | Label x -> x | Expr x -> x | Update x -> x ^"=true")
  | True -> "true"
  | False -> "false"
  | _ as s -> 
    let () = output_hum stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non And proposition type when building transition labels" ))
(* Make transitions *)
let make_transitions init guard ob = function
  | (({name=n;incoming=i}),tlabel,guards) -> 
    if i <> [] then
      let () = List.iter2 (fun x g -> 
	let () = B.add_string ob "<transition>\n" in
	let () = B.add_string ob ("<source ref=\"" ^ x ^"\"/>\n") in
	let () = B.add_string ob ("<target ref=\"" ^ n ^ "\"/>\n") in
	(* This is where the labels go! *)
	let () = B.add_string ob "<label kind=\"guard\">" in
	if x = init then
	  B.add_string ob (label (solve_logic (And(guard,g))))
	else
	  B.add_string ob (label g);
	let () = B.add_string ob "\n</label>\n" in
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
let make_xml stnode init lgn = 
  let ob = B.create(10000) in
  let () = B.add_string ob "<template>\n" in
  counter := !counter + 1;
  let () = B.add_string ob ("<name>Template" ^ (string_of_int !counter) ^"</name>\n") in
  ss := !ss ^ "Process" ^ (string_of_int !counter) ^ " = Template" ^ (string_of_int !counter) ^ "();\n";
  ss1 := ("Process" ^ (string_of_int !counter)) :: !ss1;
  (* make the nodes *)
  (* let () = make_init ob in *)
  let () = List.iter (make_locations ob) (List.map (fun x -> (x.node,x.tlabels)) lgn) in
  let () = B.add_string ob ("<init ref=\"" ^ init ^ "\"/>\n") in
  (* Make transitions *)
  let () = List.iter (make_transitions init (List.hd stnode.guards) ob) (List.map (fun x -> (x.node,x.tlabels,x.guards)) lgn) in
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
