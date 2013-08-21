module List = Batteries.List

module SS = Sexplib.Sexp
module SSL = Sexplib.Std

module PL = PropositionalLogic

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
  (* This map is for each clock-domain *)
  let uppaal_automatas = List.map Uppaal.make_xml labeled_buchi_automatas in
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
    let (s,f,se,t,fo) = PropositionalLogic.dltl stmt in
    (* let fo = PL.Or(PL.NextTime(PL.Not (PL.Proposition "L2")), PL.NextTime(PL.Proposition "L1")) in *)
    let fo = PL.And(PL.Proposition "l", PL.NextTime(PL.Proposition "l")) in
    let () = print_endline "The partial formulas and their BAs" in
    let () = SS.output_hum stdout (PropositionalLogic.sexp_of_logic (PropositionalLogic.solve_logic (PropositionalLogic.push_not (fo)))) in
    let () = print_endline "\n\n\n" in
    let ba = TableauBuchiAutomataGeneration.create_graph (PropositionalLogic.solve_logic (PropositionalLogic.push_not (fo))) in
    let () = print_endline "Nodes in the nodes set" in
    let () = List.iter (fun x -> SS.output_hum stdout (TableauBuchiAutomataGeneration.sexp_of_graph_node x); print_endline"\n") ba in
    let lba = TableauBuchiAutomataGeneration.add_labels (PropositionalLogic.solve_logic (PropositionalLogic.push_not (fo))) ba in
    List.iter (fun x -> SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x))[lba])stmt) [ast] in
    let () = print_endline "\n\n\n" in
    ()
ELSE() ENDIF in
  ()
    
with
| End_of_file -> exit 0
| Sys_error  _ -> print_endline usage_msg
| _ as s -> raise s
