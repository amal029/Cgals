open PropositionalLogic
open Sexplib
open Std
open Sexp

module List = Batteries.List

exception Internal_error of string
type graph_node = {mutable name:string; mutable father:string; mutable incoming: string list;
		   mutable neew: logic list; mutable old:logic list; mutable next: logic list}
with sexp

let counter = ref 0

let new_name () = 
  counter := !counter + 1; 
  "N" ^ (string_of_int !counter)

let negate = function
  | Proposition x -> Not (Proposition x)
  | Not (Proposition x) -> Proposition x
  | _ -> raise (Internal_error "Don't know how to negate non-proposition clauses!!")

let rec expand node nodes_set = 
  match node.neew with
  | [] -> 
    (try
       let shared_node = List.find (fun x -> (x.old = node.old) && (node.next = x.next)) !nodes_set in
       let () = shared_node.incoming <- shared_node.incoming @ node.incoming in
       let () = IFDEF DEBUG THEN print_endline "almost done" ELSE () ENDIF in ()
     with
     | Not_found -> 
       let () = IFDEF DEBUG THEN print_endline "not done but node.neew = NULL" ELSE () ENDIF in
       nodes_set := node :: !nodes_set;
       let nn = new_name () in
       let st = {name=nn; father=nn;
		 incoming=[node.name];
		 neew=node.next;
		 old=[]; next=[]} in
       let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_graph_node st); print_endline "" ELSE () ENDIF in
       expand st nodes_set)
  | _ -> 
    (* Here n stands for $\nu$ the greek letter *)
    let n = List.hd node.neew in
    let () = node.neew <- List.remove_all node.neew n in
    let () = IFDEF SDEBUG THEN output_hum stdout (sexp_of_list (PropositionalLogic.sexp_of_logic) node.neew); print_endline "******";
      ELSE () ENDIF in
    let () = (match n with
      | Proposition _
      | Not (Proposition _)
      | True
      | False -> 
	(* Contradiction, abondon! *)
	if n = False || List.exists (fun x -> x = (negate n)) node.old then ()
	else 
	  let () = node.old <- node.old @ [n] in
	  let () = IFDEF DEBUG THEN 
	      let () = output_hum stdout (sexp_of_graph_node node) in
	      print_endline "No contradiction yet!" ELSE () ENDIF in
	  expand node nodes_set
      | And (x,y) -> 
	let () = IFDEF DEBUG THEN 
	  print_endline "\n\n\n\nIn AND CLAUSE";
	  output_hum stdout (PropositionalLogic.sexp_of_logic x); 
	  print_endline "\nAND";
	  output_hum stdout (PropositionalLogic.sexp_of_logic y); 
	  print_endline "\n\n\n\n";
	  ELSE () ENDIF in
	let ups = ref [x;y] in
	let () = List.iter (fun y -> ups := (List.drop_while (fun x -> x = y) !ups)) node.old in
	let st = {name=node.name; father=node.name;
		  incoming=node.incoming;
		  neew=node.neew @ !ups;
		  old=node.old @ [n]; next=node.next} in
	let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_graph_node st) ELSE () ENDIF in
	expand st nodes_set
      | Or (x,y) -> 
	let () = IFDEF DEBUG THEN 
	  print_endline "\n\n\n\n\nIn OR CLAUSE";
	  output_hum stdout (PropositionalLogic.sexp_of_logic x); 
	  print_endline "\nOR";
	  output_hum stdout (PropositionalLogic.sexp_of_logic y); 
	  print_endline "\n\n\n\n\n";
	  ELSE () ENDIF in
	let nn1 = new_name () in
	let ups = ref [x] in
	let () = List.iter (fun y -> ups := (List.drop_while (fun x -> x = y) !ups)) node.old in
	let node1 = {name=nn1;father=node.name;incoming=node.incoming;
		     neew=node.neew @ !ups;old=node.old @ [n];
		     next=node.next} in
	let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_graph_node node1) ELSE () ENDIF in
	let nn2 = new_name () in
	let ups = ref [y] in
	let () = List.iter (fun y -> ups := (List.drop_while (fun x -> x = y) !ups)) node.old in
	let node2 = {name=nn2;father=node.name;incoming=node.incoming;
		     neew=node.neew @ !ups;old=node.old @ [n];
		     next=node.next} in
	let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_graph_node node2) ELSE () ENDIF in
	let () = expand node1 nodes_set in
	expand node2 nodes_set
      | NextTime x -> 
	let node = {name=node.name;father=node.name;incoming=node.incoming;
		    neew=node.neew;old=node.old@[n];
		    next=node.next@[x]} in
	expand node nodes_set
      | Brackets x -> expand node nodes_set
      | _ -> raise (Internal_error "Don't know how to handle the formula!")
    ) in
    ()

let create_graph formula = 
  let nn = new_name () in
  let st = {name=nn; father=nn;
	    incoming=["init"];
	    neew=[formula];
	    old=[]; next=[]} in
  let nodes_set = ref [] in
  let () = expand st nodes_set in
  let () = IFDEF DEBUG THEN print_endline "done expand" ELSE () ENDIF in
  !nodes_set
