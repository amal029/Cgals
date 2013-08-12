open Batteries;;
let usage_msg = "Usage: systemjc [options] <filename>\nsee -help for more options" in
try
  let file_name = ref "" in
  let () = Arg.parse [] (fun x -> file_name := x) usage_msg in

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
  let (insts,enters) = PropositionalLogic.build_propositional_tree_logic ast in
  let () = IFDEF DEBUG THEN 
    let () = print_endline "Inst propositional logic tree: " in
    List.iter print_endline (List.map PropositionalLogic.print insts) ELSE () ENDIF in
  let () = IFDEF DEBUG THEN 
    let () = print_endline "Enter propositional logic tree: " in
    List.iter print_endline (List.map PropositionalLogic.print enters) ELSE () ENDIF in 
  ()
  
with
| End_of_file -> exit 0
| Sys_error  _ -> print_endline usage_msg
| _ as s -> raise s
