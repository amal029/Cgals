module List = Batteries.List
module Hashtbl = Batteries.Hashtbl

module SS = Sexplib.Sexp
module SSL = Sexplib.Std

module PL = PropositionalLogic
open TableauBuchiAutomataGeneration

let rec map5 f a b c d e = 
  match (a,b,c,d,e) with
  | ([],[],[],[],[]) -> []
  | ((h1::t1),(h2::t2),(h3::t3),(h4::t4), (h5::t5)) -> (f h1 h2 h3 h4 h5) :: map5 f t1 t2 t3 t4 t5
  | _ -> failwith "Lists not of equal length"

let usage_msg = "Usage: systemjc [options] <filename>\nsee -help for more options" in
try
  let file_name = ref "" in
  let uppaal = ref "" in
  let promela = ref "" in
  let () = Arg.parse [
    ("-uppaal", Arg.Set_string uppaal, " The name of the uppaal xml output file");
    ("-promela", Arg.Set_string promela, " The name of the promela output file")] 
    (fun x -> file_name := x) usage_msg in

  (* Initialize the error reporting structures *)
  let in_chan = open_in !file_name in
  let () = print_endline "....Lexing and parsing..." in
  let lexbuf = Lexing.from_channel in_chan in
  let ast = Parser.ast Lexer.lexer lexbuf in
  (* Close the input channel *)
  let () = close_in in_chan in 
  let () = print_endline "....Rewriting the ast ..." in
  let channels = List.sort_unique compare (List.flatten (List.map Systemj.collect_channels 
							   (match ast with |Systemj.Apar(x,_)->x))) in
  let () = IFDEF DEBUG THEN SS.output_hum Pervasives.stdout (Systemj.sexp_of_ast ast); print_endline "" ELSE () ENDIF in
  let ast = PropositionalLogic.rewrite_ast ast in
  let () = print_endline "....Building Propositional logic trees ..." in
  let ltls = PropositionalLogic.build_propositional_tree_logic ast in
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
    let () = SS.output_hum Pervasives.stdout (PropositionalLogic.sexp_of_logic x) in
    print_endline "\n\n\n\n\n\n-----------------------------------------------\n\n\n\n") ltls ELSE () ENDIF in
  let () = print_endline "....Building Buchi Automata ..." in
  let buchi_automatas = List.mapi TableauBuchiAutomataGeneration.create_graph ltls in
  let labeled_buchi_automatas = List.map2 TableauBuchiAutomataGeneration.add_labels ltls buchi_automatas in
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
    let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
    print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
  let () = List.iter ModelSystem.propagate_guards_from_st labeled_buchi_automatas in
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
    let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
    print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
  let init = ref [] in
  let labeled_buchi_automatas = 
    List.map (fun x -> 
      let () = List.iter ModelSystem.make x in
      let () = List.iter ModelSystem.replace (List.of_enum (Hashtbl.values ModelSystem.tbl)) in 
      let () = Hashtbl.clear ModelSystem.replaced in 
      (* let () = Hashtbl.clear ModelSystem.guards in  *)
      let ret = List.of_enum (Hashtbl.values ModelSystem.tbl) in
      let () = Hashtbl.clear ModelSystem.tbl in
      let ret = List.filter (fun {node=n} -> n.old <> []) ret in
      let () = flush_all () in
      let st_node = List.find (fun {tlabels=t} -> (match t with | PL.Proposition (PL.Label x) -> x = "st" | _ -> false)) ret in
      init := st_node.node.name :: !init;
      let () = print_endline "....Building SystemJ model......" in
      let () = IFDEF DEBUG THEN List.iter (fun x -> 
	let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
	print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
      let () = List.iter (fun ({node=n} as ln) -> 
	let gg = ref [] in
	let ig = ref [] in
	for c = 0 to (List.length ln.guards)-1 do
	  if (List.nth n.incoming c) <> "Init" then
	    gg := !gg @ [(List.nth ln.guards c)]
	  else
	    ig := !ig @ [(List.nth ln.guards c)]
	done;
	if !ig <> [] then
	  (* This is the only way this should be allowed: 1.) If there
	     are multiple Init's then that means you could have run this
	     thing with an || 2.) But, if there is a parent node, then
	     that node needs to have been true for this node to have
	     been executed. -- At least, that's the theory!
	  *)
	  let ig = List.reduce (fun x y -> PL.Or(x,y)) !ig in
	  gg := List.map (fun x -> PL.solve_logic (PL.And (x,ig))) !gg;
	  ln.guards <- !gg;
	  (* This is deleting the rest of the nodes with incoming as Init *)
	  (* n.incoming <- List.remove_all n.incoming "Init"; *)
      ) ret in
      (* There are other nodes without "st", these can be logic
	 formulas, in that case we need to find the nodes, which these
	 nodes are a subformula of!  Note: 1.) I only look at Init nodes
	 in this case.  2.) Replace the nodes with the new set of
	 incoming nodes 3.) FIXME (IMP): If no replacements are possible
	 then these nodes and their corresponding guards should be
	 delted!  *)
      let () = print_endline "....Building FUCKING SystemJ model......" in
      let () = IFDEF DEBUG THEN List.iter (fun x -> 
	let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
	print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
      let torep = (List.filter(fun {tlabels=t} -> (match t with | PL.Proposition (PL.Label x) -> x <> "st" | _ -> true))
      		     (List.filter (fun{node=n} -> n.incoming=["Init"])ret)) in
      let () = List.iter(fun {node=n} -> n.incoming <- List.remove_all n.incoming "Init";) ret in
      let (_,ret) = List.partition (fun {node=n} -> n.incoming = [] && n.name <> st_node.node.name) ret in
      let () = List.iter (ModelSystem.find_subformula_equivalents ret) torep in
      ret) labeled_buchi_automatas in
  (* This map is for each clock-domain *)
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
    let () = print_endline "....Building SystemJ model......" in
    let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
    print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
  let () = 
    if !uppaal = "" then
      (* Buffer.output_buffer stdout uppaal_automata *)
      ()
    else 
      try
	let uppaal_automatas = map5 Uppaal.make_xml (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_signal_declarations x)
	  (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_input_signal_declarations x)
	  (List.init (List.length labeled_buchi_automatas) (fun x -> x)) (List.rev !init) labeled_buchi_automatas in
	let strings = Buffer.create(10000) in
	let () = List.iter (Buffer.add_buffer strings) uppaal_automatas in
	let () = IFDEF DEBUG THEN print_endline (string_of_int (List.length channels)) ELSE () ENDIF in
	let uppaal_automata = Uppaal.make_uppaal channels strings in
	(* Write to output file if the -o argument is given, else write to stdout *)
	let fd = open_out !uppaal in
	let () = Buffer.output_buffer fd uppaal_automata in
	close_out fd
      with
      | Sys_error _ as s -> raise s
  in
  let () = 
    if !promela = "" then
      ()
    else 
      try
	let fd = open_out !promela in
	let promela_model = map5 Promela.make_promela (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_signal_declarations x)
	  (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_input_signal_declarations x)
	  (List.init (List.length labeled_buchi_automatas) (fun x -> x)) (List.rev !init) labeled_buchi_automatas in
	(* make the channel declarations in the global space!! *)
	let promela_channels = List.fold_left Pretty.append Pretty.empty (List.map (fun x -> Pretty.text ("bool "^x^";\n"))channels) in
	let () = Pretty.print ~output:(output_string fd) (Pretty.append promela_channels (List.reduce Pretty.append promela_model)) in
	close_out fd;
      with
      | Sys_error _ as s -> raise s in ()
with
| End_of_file -> exit 0
| Sys_error  _ -> print_endline usage_msg
| _ as s -> raise s
