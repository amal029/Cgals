open PropositionalLogic
module List = Batteries.List

let graph_node = {name:string; father:string; incoming: string list;
		 neew: logic list; old:logic list; next: logic list}

let counter = ref 0

let new_name () = 
  counter := !counter + 1; 
  "N" ^ (string_of_int !counter)

(* TODO: Complete me!  *)
let expand node node_set = node_set

let create_graph formula = 
  let nn = new_name () in
  let st = {name=nn; father=nn;
	    incoming=["init"];
	    neew=[formula];
	    old=[]; next=[]} in
  expand(st,[])
