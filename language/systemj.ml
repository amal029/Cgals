(* This is the pure kernel language of SystemJ:
   1.) There is no data => 
   a.) There are no valued signals and 
   b.) There are no Java stmts
   Wed Jul 31 09:26:33 NZST 2013
   Avinash Malik
   
   The language goes a bit beyond SystemJ/Esterel towards, VHDL.
*)

(* The current position for error reporting *)
type line = int
type column = int

type symbol =
| Symbol of string * (line * column)

type expr =
| Esymbol of symbol * (line * column)
| And of expr * expr * (line * column)
| Or of expr * expr * (line * column)
| Brackets of expr * (line * column)

type io = 
| Input
| Output

type sysj_bool =
| True
| False

type stmt = 
| Block of stmt list * (line * column)
| Pause of string option * (line * column)
| Emit of symbol * (line * column)
| Present of expr * stmt * stmt option * (line * column)
| Trap of symbol * stmt * (line * column)
| Signal of io option * symbol * (line * column)
| Channel of io * symbol * (line * column)
| Spar of stmt list * (line * column)
| Exit of symbol * (line * column)
| Abort of expr * stmt * (line * column)
| Suspend of expr * stmt * (line * column)
| Send of symbol * (line * column)
| Receive of symbol * (line * column)
| While of sysj_bool * stmt * (line * column)
| Noop

type ast =
| Apar of stmt list * (line * column)


let print_symbol = function
  | Symbol (x,ln) -> x

let print_expr x = "EXPR HERE"

let rec print_stmt = function
  | Block (x,ln) -> 
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = List.iter print_stmt x in ()
  | Pause (Some x, ln) -> 
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = print_endline ("Pause: " ^ x) in ()
  | Pause (None, ln) -> 
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = print_endline "Pause: " in ()
  | Emit (x,ln) ->
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = print_endline ("emit " ^(print_symbol x)) in ()
  | Present (expr,s,None,ln) ->
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = print_endline ("Present (" ^ (print_expr expr) ^ ") {") in
    let () = print_stmt s in
    let () = print_endline "}" in ()
  | Present (expr,s,Some e,ln) ->
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = print_endline ("Present (" ^ (print_expr expr) ^ ") {") in
    let () = print_stmt s in
    let () = print_endline "}" in 
    let () = print_endline "else {" in
    let () = print_stmt e in
    let () = print_endline "}" in ()
  | Trap (s,st,ln) ->
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = print_endline ("trap (" ^ (print_symbol s) ^ "){") in
    let () = print_stmt st in
    let () = print_endline "}" in ()
  | Signal (_,s,ln) ->
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = print_endline ("signal " ^ (print_symbol s)) in () 
  | Channel (_,s,ln) ->
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = print_endline ("channel " ^ (print_symbol s)) in () 
  | Spar (ll,ln) -> 
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = List.iter print_stmt ll in ()
  | _ -> print_endline "Need to complete this printing routine!"


let print = function
  | Apar (x,ln) -> 
    let () = print_string ((Reporting.get_line_and_column ln) ^ " : ") in
    let () = List.iter print_stmt x in ()
