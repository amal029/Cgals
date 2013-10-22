open PropositionalLogic
open Sexplib
open Std
open Sexp

module List = Batteries.List

exception Internal_error of string
type graph_node = {mutable name:string; mutable father:string; mutable incoming: string list; 
                   mutable incoming_chan: (string * Systemj.tchan) list;
		   mutable neew: logic list; mutable old:logic list; mutable next: logic list}
with sexp

type labeled_graph_node = {node: graph_node; mutable tlabels: logic; 
			   mutable guards: logic list; tls : logic list}
with sexp

let counter = ref 0

let new_name () = 
  counter := !counter + 1; 
  "N" ^ (string_of_int !counter)

let negate = function
  | Proposition (x,p) -> Not (Proposition (x,p))
  | Not (Proposition (x,p)) -> Proposition (x,p)
  | True -> False
  | False -> True
  | _ as s -> 
    output_hum stdout (sexp_of_logic s); print_endline "";
    print_endline "^^^^^^^^^^";
    raise (Internal_error "Don't know how to negate non-proposition clauses!!")

let rec expand index node nodes_set = 
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
         incoming=[node.name]; incoming_chan=[];
		 neew=node.next;
		 old=[]; next=[]} in
       expand index st nodes_set)
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
	let s = 
	  if (match n with | Proposition (Expr t,_) -> t.[0] = '$' | _ -> false) then
	    try 
	      (Hashtbl.find (List.at !update_tuple_proposition_ll index) n)
	    with | _ as s ->
	      print_endline ("Index: " ^ (string_of_int index));
	      output_hum stdout (sexp_of_logic n);
	      raise s
	  else n in
	if n = False || List.exists (fun x -> x = (negate n)) node.old 
	|| List.exists (fun x -> 
	  let tt = if (match x with | Proposition (Expr t,_) -> t.[0] = '$' | _ -> false) then
	      try 
		(Hashtbl.find (List.at !update_tuple_proposition_ll index) x)
	      with | _ as s ->
		output_hum stdout (sexp_of_logic x);
		raise s
	    else x in
	  tt = (negate s)
	) node.old then
	  (* TODO: Need to change this *)
	  (* Raise an error stating that there is a contradiction in the formula!! *)
	  if n <> False then
	    if s = n then
	      let () = output_hum stdout (sexp_of_logic (negate n)) in
	      let () = print_string " /\\ " in
	      let () = output_hum stdout (sexp_of_logic n) in
	      let () = print_endline "\n^^^^^^^^^^^^^^^^^^" in
	      print_endline "Warning : Contradiction";
	    else
	      let () = output_hum stdout (sexp_of_logic (negate s)) in
	      let () = print_string " /\\ " in
	      let () = output_hum stdout (sexp_of_logic s) in
	      let () = print_endline "\n^^^^^^^^^^^^^^^^^^" in
	      print_endline "Warning : Contradiction";
	  else
	    let () =  print_endline "Warning: False proposition" in
	    ()
	else 
	  let () = node.old <- node.old @ [n] in expand index node nodes_set
      | And (x,y) -> 
	let ups = ref [x;y] in
	let () = List.iter (fun y -> ups := (List.remove_all !ups y)) node.old in
	let st = {name=node.name; father=node.name;
            incoming=node.incoming; incoming_chan=[];
		  neew=node.neew @ !ups;
		  old=node.old @ [n]; next=node.next} in
	expand index st nodes_set
      | Or (x,y) -> 
	let nn1 = new_name () in
	let ups = ref [x] in
	let () = List.iter (fun y -> ups := (List.remove_all !ups y)) node.old in
    let node1 = {name=nn1;father=node.name;incoming=node.incoming;incoming_chan=[];
		     neew=node.neew @ !ups;old=node.old @ [n];
		     next=node.next} in
	let nn2 = new_name () in
	let ups = ref [y] in
	let () = List.iter (fun y -> ups := (List.remove_all !ups y)) node.old in
	(* let () = List.iter (fun y -> ups := (List.drop_while (fun x -> x = y) !ups)) node.old in *)
    let node2 = {name=nn2;father=node.name;incoming=node.incoming;incoming_chan=[];
		     neew=node.neew @ !ups;old=node.old @ [n];
		     next=node.next} in
	let () = expand index node1 nodes_set in
	expand index node2 nodes_set
      | NextTime x -> 
              let node = {name=node.name;father=node.name;incoming=node.incoming;incoming_chan=[];
		    neew=node.neew;old=node.old@[n];
		    next=node.next@[x]} in
	expand index node nodes_set
      | Brackets x as s -> 
	output_hum stderr (sexp_of_logic s);
	print_endline "\n^^^^^^^^^^^^^^^^^^^^^^^^^^^";
	raise (Internal_error "Brackets should have been removed in the above formula")
	(* expand index node nodes_set *)
      | _ as s -> 
	output_hum stdout (sexp_of_logic s); print_endline "";
	print_endline "^^^^^^^^^^";
	raise (Internal_error "Don't know how to handle the formula!")
    ) in
    ()

let create_graph index formula = 
  let nn = new_name () in
  let st = {name=nn; father=nn;
      incoming=["Init"];incoming_chan=[];
	    neew=[formula];
	    old=[]; next=[]} in
  let nodes_set = ref [] in
  let () = expand index st nodes_set in
  !nodes_set

let state_label propositions = function
  | {name=n;old=o} as s -> 
    let pos_props = ref [] in
    let () = List.iter (fun x ->  
      pos_props := !pos_props @ List.filter (fun y -> x=y) o;
    ) propositions in
    let pos_props = (List.sort_unique compare) !pos_props in
    let neg_props = List.filter (fun x -> (match x with | Not(Proposition _) -> true | _ -> false)) o in
    let (labels,g) = List.partition (fun x -> (match x with | Proposition (x,_) | Not (Proposition (x,_))
      -> (match x with | Label _ -> true | _ -> false) | _ -> false)) (pos_props @ neg_props) in
    let tls = if labels <> [] then List.reduce (fun x y -> And(x,y)) labels else True in
    let g = if g <> [] then List.reduce (fun x y -> solve_logic (And(x,y))) g else True in
    let g = BatArray.to_list (BatArray.make (List.length s.incoming) g) in
    {node=s;tlabels=solve_logic tls;guards=g; tls=labels}

let add_labels formula nodes_set =
  (* Get all the propositions used in the formula *)
  let propositions = props formula in
  (* Remove the duplicates *)
  let propositions = List.sort_unique compare propositions in
  let lba = List.map (state_label propositions) nodes_set in
  lba
