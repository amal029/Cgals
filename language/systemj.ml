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
