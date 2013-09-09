(* This is the pure kernel language of SystemJ:
   1.) There is no data => 
   a.) There are no valued signals and 
   b.) There are no Java stmts
   Wed Jul 31 09:26:33 NZST 2013
   Avinash Malik
   
   The language goes a bit beyond SystemJ/Esterel towards, VHDL.
*)

(* The current position for error reporting *)
open Sexplib.Std

type line = int
with sexp
type column = int
with sexp


type symbol =
| Symbol of string * (line * column)
with sexp

type expr =
| Esymbol of symbol * (line * column)
| And of expr * expr * (line * column)
| Or of expr * expr * (line * column)
| Not of expr * (line * column)
| Brackets of expr * (line * column)
with sexp

type io = 
| Input
| Output
with sexp

type sysj_bool =
| True
| False
with sexp

type stmt = 
| Block of stmt list * (line * column)
| Pause of string option * (line * column)
| Emit of symbol * string option * (line * column)
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
with sexp
type ast =
| Apar of stmt list * (line * column)
with sexp

exception Internal_error of string

let rec collect_channels = function
  | Pause _ | Emit _ | Exit _ | Noop
  | Send _ | Receive _
  | Signal _ -> []
  | Channel (_,(Symbol (x,_)),_) -> [(x^"_req");(x^"_ack")]
  | Present (_,s,None,_) -> collect_channels s
  | Present (_,s,Some x,_) -> collect_channels s @ collect_channels x
  | Trap (_,s,_) -> collect_channels s
  | Block (s,_) 
  | Spar (s,_) -> List.flatten (List.map collect_channels s)
  | Abort (_,s,_) -> collect_channels s
  | Suspend (_,s,_) -> collect_channels s
  | While (_,s,_) -> collect_channels s

let rec collect_signal_declarations = function
  | Pause _ | Emit _ | Exit _ | Noop
  | Channel _ -> []
  | Signal (_,Symbol (s,_),_) -> [s]
  | Present (_,s,None,_) -> collect_signal_declarations s
  | Present (_,s,Some x,_) -> collect_signal_declarations s @ collect_signal_declarations x
  | Trap (_,s,_) -> collect_signal_declarations s
  | Block (s,_) 
  | Spar (s,_) -> List.flatten (List.map collect_signal_declarations s)
  | Abort (_,s,_) -> collect_signal_declarations s
  | Suspend (_,s,_) -> collect_signal_declarations s
  | While (_,s,_) -> collect_signal_declarations s
  | Send _ | Receive _ -> raise (Internal_error "Collect signals: Cannot get send/receive after re-write!!")
