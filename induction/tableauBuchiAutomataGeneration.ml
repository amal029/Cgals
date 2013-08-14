open PropositionalLogic
module List = Batteries.List

exception Internal_error of string
type graph_node = {mutable name:string; mutable father:string; mutable incoming: string list;
		   mutable neew: logic list; mutable old:logic list; mutable next: logic list}

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
       shared_node.incoming <- shared_node.incoming @ node.incoming
     with
     | Not_found -> 
       nodes_set := node :: !nodes_set;
       let nn = new_name () in
       let st = {name=nn; father=nn;
		 incoming=node.incoming;
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
	if n = False || List.exists (fun x -> x = (negate n)) node.old then ()
	else 
	  let () = node.old <- node.old @ [n] in
	  expand node nodes_set
      | And (x,y) -> 
	let ups = ref [x;y] in
	let () = List.iter (fun y -> ups := (List.drop_while (fun x -> x = y) !ups)) node.old in
	let st = {name=node.name; father=node.name;
		  incoming=node.incoming;
		  neew=node.neew @ !ups;
		  old=node.old @ [n]; next=node.next} in
	expand st nodes_set
      | Or (x,y) -> 
	let nn1 = new_name () in
	let ups = ref [x] in
	let () = List.iter (fun y -> ups := (List.drop_while (fun x -> x = y) !ups)) node.old in
	let node1 = {name=nn1;father=node.name;incoming=node.incoming;
		     neew=node.neew @ !ups;old=node.old @ [n];
		     next=node.next} in
	let nn2 = new_name () in
	let ups = ref [y] in
	let () = List.iter (fun y -> ups := (List.drop_while (fun x -> x = y) !ups)) node.old in
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
	    incoming=["init"];
	    neew=[formula];
	    old=[]; next=[]} in
  let nodes_set = ref [] in
  expand st nodes_set
