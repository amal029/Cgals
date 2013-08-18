(* This file creates the Uppaal timed-automata for model-checking and
   verification from SystemJ program. Notice that this file produces XML
   directly, no pretty-printing is done, because of lack of time. Later
   the xml-light library should be used to produce this automata.

   Author: Avinash Malik 

   Sat Aug 17 10:47:06 NZST 2013

*)
module List = Batteries.List
module B = Buffer

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration

exception Internal_error of string

(* Make transitions *)
(* TODO: The updates and the guards need to be added *)
let make_transitions ob = function
  | {name=n;incoming=i} -> 
    let () = List.iter (fun x -> 
      let () = B.add_string ob "<transition>\n" in
      let () = B.add_string ob ("<source ref=\"" ^ x ^"\"/>\n") in
      let () = B.add_string ob ("<target ref=\"" ^ n ^ "\"/>\n") in
      let () = B.add_string ob "</transition>\n" in () )i in ()

(* Uppaal locations for the networked automata system*)
let make_locations ob = function
  | {name=n} -> 
    let () = B.add_string ob ("<location id=\"" ^ n ^"\">\n") in
    let () = B.add_string ob ("<name>" ^ n ^"</name>\n") in
    let () = B.add_string ob ("<committed/>\n</location>\n") in
    ()

let make_init ob = 
  let () = B.add_string ob "<location id=\"Init\">\n" in
  let () = B.add_string ob "<name>Init</name>\n" in
  let () = B.add_string ob "<committed/></location>\n" in
  ()

let counter = ref 0
let ss = ref "" 
let ss1 = ref []

(* Outputs the XML file for Uppaal model-checker *)
(* This is for each clock-domain *)
let make_xml lgn = 
  let ob = B.create(10000) in
  let () = B.add_string ob "<template>\n" in
  counter := !counter + 1;
  let () = B.add_string ob ("<name>Template" ^ (string_of_int !counter) ^"</name>\n") in
  ss := !ss ^ "Process" ^ (string_of_int !counter) ^ " = Template" ^ (string_of_int !counter) ^ "();\n";
  ss1 := ("Process" ^ (string_of_int !counter)) :: !ss1;
  (* make the nodes *)
  let () = make_init ob in
  let () = List.iter (make_locations ob) (List.map (fun x -> x.node) lgn) in
  let () = B.add_string ob "<init ref=\"Init\"/>\n" in
  (* Make transitions *)
  let () = List.iter (make_transitions ob) (List.map (fun x -> x.node) lgn) in
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
