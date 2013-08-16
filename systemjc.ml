module List = Batteries.List

module SS = Sexplib.Sexp
module SSL = Sexplib.Std

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
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
    let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_graph_node x) in
    print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") buchi_automatas ELSE () ENDIF in
  let uppaal_automatas = List.map Uppaal.make_xml buchi_automatas in
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
  ()
    
with
| End_of_file -> exit 0
| Sys_error  _ -> print_endline usage_msg
| _ as s -> raise s
