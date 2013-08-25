module List = Batteries.List
module Hashtbl = Batteries.Hashtbl

module SS = Sexplib.Sexp
module SSL = Sexplib.Std

module PL = PropositionalLogic
open TableauBuchiAutomataGeneration

let rec map3 f a b c = 
  match (a,b,c) with
  | ([],[],[]) -> []
  | ((h1::t1),(h2::t2),(h3::t3)) -> (f h1 h2 h3) :: map3 f t1 t2 t3
  | _ -> failwith "Lists not of equal length"

let usage_msg = "Usage: systemjc [options] <filename>\nsee -help for more options" in
try
  let file_name = ref "" in
  let output = ref "" in
  let () = Arg.parse [
    ("-uppaal", Arg.Set_string output, " The name of the uppaal xml output file");] 
    (fun x -> file_name := x) usage_msg in

  (* Initialize the error reporting structures *)
  let in_chan = open_in !file_name in
  let () = print_endline "....Lexing and parsing..." in
  let lexbuf = Lexing.from_channel in_chan in
  let ast = Parser.ast Lexer.lexer lexbuf in
  (* Close the input channel *)
  let () = close_in in_chan in 
  let () = print_endline "....Rewriting the ast ..." in
  let ast = PropositionalLogic.rewrite_ast ast in
  let () = print_endline "....Building Propositional logic trees ..." in
  let ltls = PropositionalLogic.build_propositional_tree_logic ast in
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
    let () = SS.output_hum Pervasives.stdout (PropositionalLogic.sexp_of_logic x) in
    print_endline "\n\n\n\n\n\n-----------------------------------------------\n\n\n\n") ltls ELSE () ENDIF in
  let () = print_endline "....Building Buchi Automata ..." in
  let buchi_automatas = List.map TableauBuchiAutomataGeneration.create_graph ltls in
  let labeled_buchi_automatas = List.map2 TableauBuchiAutomataGeneration.add_labels ltls buchi_automatas in
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
    let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
    print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
  let init = ref [] in
  let sts = ref [] in
  let labeled_buchi_automatas = 
    List.map (fun x -> 
      let () = List.iter ModelSystem.make x in
      let () = List.iter ModelSystem.replace (List.of_enum (Hashtbl.values ModelSystem.tbl)) in 
      let () = Hashtbl.clear ModelSystem.replaced in 
      let () = Hashtbl.clear ModelSystem.guards in 
      let ret = List.of_enum (Hashtbl.values ModelSystem.tbl) in
      let () = Hashtbl.clear ModelSystem.tbl in
      let ret = List.filter (fun {node=n} -> n.old <> []) ret in
      let st_node = List.find (fun {tlabels=t} -> (match t with | PL.Proposition (PL.Label x) -> x = "st" | _ -> false)) ret in
      sts := !sts @[st_node]; 
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
	  let ig = List.reduce (fun x y -> PL.And(x,y)) !ig in
	  if ln <> st_node then begin
	    gg := List.map (fun x -> PL.solve_logic (PL.And (x,ig))) !gg;
	    ln.guards <- !gg;
	  end
	  else ln.guards <- [PL.solve_logic ig];
	  n.incoming <- List.remove_all n.incoming "Init";
      ) ret in
      let (_,ret) = List.partition (fun {node=n} -> n.incoming = [] && n.name <> st_node.node.name) ret in
      ret) labeled_buchi_automatas in
  (* This map is for each clock-domain *)
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
    let () = print_endline "....Building SystemJ model......" in
    let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
    print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
  let uppaal_automatas = map3 Uppaal.make_xml !sts (List.rev !init) labeled_buchi_automatas in
  let strings = Buffer.create(10000) in
  let () = List.iter (fun x -> Buffer.add_buffer strings x) uppaal_automatas in
  let uppaal_automata = Uppaal.make_uppaal strings in
  (* Write to output file if the -o argument is given, else write to stdout *)
  let () = 
    if !output = "" then
      Buffer.output_buffer stdout uppaal_automata
    else 
      try
	let fd = open_out !output in
	let () = Buffer.output_buffer fd uppaal_automata in
	close_out fd
      with
      | Sys_error _ as s -> raise s
  in
  let () = IFDEF SDEBUG THEN
let () = List.iter (fun (Systemj.Apar(stmt,_)) ->
  List.iter (fun stmt -> 
    let _ = PropositionalLogic.dltl stmt in
    (* let fo = PL.Or(PL.NextTime(PL.Not (PL.Proposition "L2")), PL.NextTime(PL.Proposition "L1")) in *)
    let fo = PL.Or(PL.And(PL.And(PL.Proposition(PL.Label "st"),PL.Proposition(PL.Label "l")),PL.NextTime(PL.Proposition(PL.Label "l"))),
		   PL.And(PL.Proposition(PL.Label "l"),PL.And(PL.NextTime(PL.Proposition(PL.Label "l")),PL.Proposition(PL.Label "l")))) in
    let () = print_endline "The partial formulas and their BAs" in
    let () = SS.output_hum stdout (PropositionalLogic.sexp_of_logic (PropositionalLogic.solve_logic (PropositionalLogic.push_not (fo)))) in
    let () = print_endline "\n\n\n" in
    let ba = TableauBuchiAutomataGeneration.create_graph (PropositionalLogic.solve_logic (PropositionalLogic.push_not (fo))) in
    (* let () = print_endline "Nodes in the nodes set" in *)
    (* let () = List.iter (fun x -> SS.output_hum stdout (TableauBuchiAutomataGeneration.sexp_of_graph_node x); print_endline"\n") ba in *)
    let lba = TableauBuchiAutomataGeneration.add_labels (PropositionalLogic.solve_logic (PropositionalLogic.push_not (fo))) ba in
    List.iter (fun x -> SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x))[lba])stmt) [ast] in
let () = print_endline "\n\n\n" in () ELSE() ENDIF in 
  ()
with
| End_of_file -> exit 0
| Sys_error  _ -> print_endline usage_msg
| _ as s -> raise s
