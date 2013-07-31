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
  let () = close_in in_chan in ()
with
| End_of_file -> exit 0
| Sys_error  _ -> print_endline usage_msg
| _ as s -> raise s
