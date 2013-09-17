open PropositionalLogic
open Sexplib
open Std
open Sexp

module List = Batteries.List

exception Internal_error of string
type graph_node = {mutable name:string; mutable father:string; mutable incoming: string list;
		   mutable neew: logic list; mutable old:logic list; mutable next: logic list}
with sexp

type labeled_graph_node = {node: graph_node; labels : logic list list; mutable tlabels: logic; 
			   mutable guards: logic list; tls : logic list}
with sexp

let counter = ref 0

let rec powerset = function
  | [] -> [[]]
  | h::t -> List.fold_left (fun xs t -> (h::t)::t::xs) [] (powerset t);;

let new_name () = 
  counter := !counter + 1; 
  "N" ^ (string_of_int !counter)

let negate = function
  | Proposition x -> Not (Proposition x)
  | Not (Proposition x) -> Proposition x
  | True -> False
  | False -> True
  | _ as s -> 
    output_hum stdout (sexp_of_logic s); print_endline "";
    print_endline "^^^^^^^^^^";
    raise (Internal_error "Don't know how to negate non-proposition clauses!!")

let rec expand node nodes_set = 
  match node.neew with
  | [] -> 
    (try
       let shared_node = List.filter (fun x -> (x.old = node.old) && (node.next = x.next)) !nodes_set in
       let shared_node = if (List.length shared_node > 1) then raise (Internal_error "More than one shared node!") 
	 else 
	   if shared_node <> [] then
	     List.hd shared_node else raise Not_found in
       let () = shared_node.incoming <- shared_node.incoming @ node.incoming in ()
     with
     | Not_found -> 
       nodes_set := node :: !nodes_set;
       let nn = new_name () in
       let st = {name=nn; father=nn;
		 incoming=[node.name];
		 neew=node.next;
		 old=[]; next=[]} in
       expand st nodes_set)
  | _ -> 
    (* Here n stands for $\nu$ the greek letter *)
    let n = List.hd node.neew in
    let () = node.neew <- List.remove_all node.neew n in
    let () = (match n with
      | Proposition _
      | Not (Proposition _)
      | True
      | False -> 
	(* Contradiction, abondon! *)
	if n = False || List.exists (fun x -> x = (negate n)) node.old then 
	  (* Raise an error stating that there is a contradiction in the formula!! *)
	  (* if n <> False then *)
	  (*   let () = output_hum stdout (sexp_of_logic (negate n)) in *)
	  (*   let () = print_string " && " in *)
	  (*   let () = output_hum stdout (sexp_of_logic n) in *)
	  (*   let () = print_endline "" in *)
	  (*   print_endline "Warning : Contradiction"; *)
	  (* else *)
	  (*   let () =  print_endline "Warning: False proposition" in *)
	    ()
	else 
	  let () = node.old <- node.old @ [n] in expand node nodes_set
      | And (x,y) -> 
	let ups = ref [x;y] in
	let () = List.iter (fun y -> ups := (List.remove_all !ups y)) node.old in
	let st = {name=node.name; father=node.name;
		  incoming=node.incoming;
		  neew=node.neew @ !ups;
		  old=node.old @ [n]; next=node.next} in
	expand st nodes_set
      | Or (x,y) -> 
	let nn1 = new_name () in
	let ups = ref [x] in
	let () = List.iter (fun y -> ups := (List.remove_all !ups y)) node.old in
	let node1 = {name=nn1;father=node.name;incoming=node.incoming;
		     neew=node.neew @ !ups;old=node.old @ [n];
		     next=node.next} in
	let nn2 = new_name () in
	let ups = ref [y] in
	let () = List.iter (fun y -> ups := (List.remove_all !ups y)) node.old in
	(* let () = List.iter (fun y -> ups := (List.drop_while (fun x -> x = y) !ups)) node.old in *)
	let node2 = {name=nn2;father=node.name;incoming=node.incoming;
		     neew=node.neew @ !ups;old=node.old @ [n];
		     next=node.next} in
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
	    incoming=["Init"];
	    neew=[formula];
	    old=[]; next=[]} in
  let nodes_set = ref [] in
  let () = expand st nodes_set in
  !nodes_set

let state_label propositions powerset = function
  | {name=n;old=o} as s -> 
    let pos_props = ref [] in
    let () = List.iter (fun x ->  
      pos_props := !pos_props @ List.filter (fun y -> x=y) o;
    ) propositions in
    let pos_props = (List.sort_unique compare) !pos_props in
    let neg_props = List.filter (fun x -> (match x with | Not(Proposition _) -> true | _ -> false)) o in
    let (labels,g) = List.partition (fun x -> (match x with | Proposition x | Not (Proposition x)
      -> (match x with | Label _ -> true | _ -> false) | _ -> false)) (pos_props @ neg_props) in
    let tls = if labels <> [] then List.reduce (fun x y -> And(x,y)) labels else True in
    let g = if g <> [] then List.reduce (fun x y -> solve_logic (And(x,y))) g else True in
    let g = BatArray.to_list (BatArray.make (List.length s.incoming) g) in
    {node=s;labels=[];tlabels=solve_logic tls;guards=g; tls=labels}

let add_labels formula nodes_set =
  (* Get all the propositions used in the formula *)
  let propositions = props formula in
  (* Remove the duplicates *)
  let propositions = List.sort_unique compare propositions in
  (* The powerset of the proposition => domain of accepting alphabets of
     the Buchi automata *)
  let prop_powerset = powerset propositions in
  let lba = List.map (state_label propositions prop_powerset) nodes_set in
  lba
