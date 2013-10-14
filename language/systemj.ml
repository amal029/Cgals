(* This is the pure kernel Cgals (seagulls):
   Sun Oct 13 10:23:14 NZDT 2013
   Avinash Malik
   
   The language only supports bounded int types.
*)

(* The current position for error reporting *)
open Sexplib.Std
module List = Batteries.List

type line = int
with sexp
type column = int
with sexp


type symbol =
| Symbol of string * (line * column)
with sexp

type datatype =
| Int8s | Int16s | Int32s
with sexp

type simpleDataExpr = 
| Plus of simpleDataExpr * simpleDataExpr * (line * column)
| Minus of simpleDataExpr * simpleDataExpr * (line * column)
| Times of simpleDataExpr * simpleDataExpr * (line * column)
| Div of simpleDataExpr * simpleDataExpr * (line * column)
| Abs of simpleDataExpr * (line * column)
| Mod of simpleDataExpr * simpleDataExpr * (line * column)
| Pow of simpleDataExpr * simpleDataExpr * (line * column)
| Rshift of simpleDataExpr * simpleDataExpr * (line * column)
| Lshift of simpleDataExpr * simpleDataExpr * (line * column)
| Const of datatype * string * (line * column)
| VarRef of symbol * (line * column)
| SignalOrChannelRef of symbol * (line * column)
| DataBrackets of simpleDataExpr * (line * column)
| Cast of datatype * simpleDataExpr  * (line * column)
| Opposite of simpleDataExpr * (line * column)
and colonDataExpr = 
(* start:end:stride *)
| ColonExpr of simpleDataExpr * simpleDataExpr * simpleDataExpr * (line * column)
with sexp

type typedSymbol =
| SimTypedSymbol of datatype * symbol * (line * column) (* Type Symbol *)
with sexp

type relDataExpr = 
| LessThan of simpleDataExpr * simpleDataExpr * (line * column)
| LessThanEqual of simpleDataExpr * simpleDataExpr * (line * column)
| GreaterThan of simpleDataExpr * simpleDataExpr * (line * column)
| GreaterThanEqual of simpleDataExpr * simpleDataExpr * (line * column)
| EqualTo of simpleDataExpr * simpleDataExpr * (line * column)
| NotEqualTo of simpleDataExpr * simpleDataExpr * (line * column)
with sexp

type expr =
| Esymbol of symbol * (line * column)
| And of expr * expr * (line * column)
| Or of expr * expr * (line * column)
| Not of expr * (line * column)
| Brackets of expr * (line * column)
| DataExpr of relDataExpr
with sexp


type io = 
| Input
| Output
with sexp

type operators =
| OpPlus
| OpTimes
with sexp

type extras = {operator:operators;data:datatype}
with sexp

type sysj_bool =
| True
| False
with sexp

type allsym = 
| AllSymbol of symbol
| AllTypedSymbol of typedSymbol
| AllSignalorChannelSymbol of symbol
with sexp

type stmt = 
| Block of stmt list * (line * column)
| Pause of string option * (line * column)
| Emit of symbol * string option * (line * column)
| Present of expr * stmt * stmt option * (line * column)
| Trap of symbol * stmt * (line * column)
| Signal of extras option * io option * symbol * (line * column)
| Channel of extras option * io * symbol * (line * column)
| Spar of stmt list * (line * column)
| Exit of symbol * (line * column)
| Abort of expr * stmt * (line * column)
| Suspend of expr * stmt * (line * column)
| Send of symbol * (line * column)
| Receive of symbol * (line * column)
| While of sysj_bool * stmt * (line * column)
| Noop
| Data of dataStmt * string option 
and dataStmt = 
| Assign of allsym * simpleDataExpr * (line * column)
| For of symbol * colonDataExpr * dataStmt * extras option * (line * column)  
| CaseDef of case * (line * column) 
| DataBlock of dataStmt list * (line * column)  
| RNoop
and case =
| Case of caseClause list * otherwise * (line * column)
and caseClause = 
| Clause of expr * dataStmt * (line * column)
and otherwise = 
| Otherwise of dataStmt * (line * column)
with sexp

type ast =
| Apar of stmt list * (line * column)
with sexp

exception Internal_error of string

let rec collect_channels = function
  | Pause _ | Emit _ | Exit _ | Noop
  | Send _ | Receive _
  | Signal _ -> []
  | Channel (_,_,(Symbol (x,_)),_) -> [(x^"_req");(x^"_ack")]
  | Present (_,s,None,_) -> collect_channels s
  | Present (_,s,Some x,_) -> collect_channels s @ collect_channels x
  | Trap (_,s,_) -> collect_channels s
  | Block (s,_) 
  | Spar (s,_) -> List.flatten (List.map collect_channels s)
  | Abort (_,s,_) -> collect_channels s
  | Suspend (_,s,_) -> collect_channels s
  | While (_,s,_) -> collect_channels s
  | Data _ -> []

let rec collect_all_signal_declarations = function
  | Pause _ | Emit _ | Exit _ | Noop
  | Channel _ -> []
  | Signal (_,io,Symbol (s,_),_) -> [s]
  | Present (_,s,None,_) -> collect_all_signal_declarations s
  | Present (_,s,Some x,_) -> collect_all_signal_declarations s @ collect_all_signal_declarations x
  | Trap (_,s,_) -> collect_all_signal_declarations s
  | Block (s,_) 
  | Spar (s,_) -> List.flatten (List.map collect_all_signal_declarations s)
  | Abort (_,s,_) -> collect_all_signal_declarations s
  | Suspend (_,s,_) -> collect_all_signal_declarations s
  | While (_,s,_) -> collect_all_signal_declarations s
  | Data _ -> []
  | Send _ | Receive _ -> raise (Internal_error "Collect signals: Cannot get send/receive after re-write!!")

let rec collect_signal_declarations = function
  | Pause _ | Emit _ | Exit _ | Noop
  | Channel _ -> []
  | Signal (_,io,Symbol (s,_),_) -> (match io with Some Input -> [] | _ -> [s])
  | Present (_,s,None,_) -> collect_signal_declarations s
  | Present (_,s,Some x,_) -> collect_signal_declarations s @ collect_signal_declarations x
  | Trap (_,s,_) -> collect_signal_declarations s
  | Block (s,_) 
  | Spar (s,_) -> List.flatten (List.map collect_signal_declarations s)
  | Abort (_,s,_) -> collect_signal_declarations s
  | Suspend (_,s,_) -> collect_signal_declarations s
  | While (_,s,_) -> collect_signal_declarations s
  | Data _ -> []
  | Send _ | Receive _ -> raise (Internal_error "Collect signals: Cannot get send/receive after re-write!!")

let rec collect_input_signal_declarations = function
  | Pause _ | Emit _ | Exit _ | Noop
  | Channel _ -> []
  | Signal (_,io,Symbol (s,_),_) -> (match io with Some Input -> [s] | _ -> [])
  | Present (_,s,None,_) -> collect_input_signal_declarations s
  | Present (_,s,Some x,_) -> collect_input_signal_declarations s @ collect_input_signal_declarations x
  | Trap (_,s,_) -> collect_input_signal_declarations s
  | Block (s,_) 
  | Spar (s,_) -> List.flatten (List.map collect_input_signal_declarations s)
  | Abort (_,s,_) -> collect_input_signal_declarations s
  | Suspend (_,s,_) -> collect_input_signal_declarations s
  | While (_,s,_) -> collect_input_signal_declarations s
  | Data _ -> []
  | Send _ | Receive _ -> raise (Internal_error "Collect signals: Cannot get send/receive after re-write!!")


let rec collect_internal_signal_declarations = function
  | Pause _ | Emit _ | Exit _ | Noop
  | Channel _ | Data _ -> []
  | Signal (_,io,Symbol (s,_),_) -> (match io with None -> [s] | _ -> [])
  | Present (_,s,None,_) -> collect_internal_signal_declarations s
  | Present (_,s,Some x,_) -> collect_internal_signal_declarations s @ collect_internal_signal_declarations x
  | Trap (_,s,_) -> collect_internal_signal_declarations s
  | Block (s,_) 
  | Spar (s,_) -> List.flatten (List.map collect_internal_signal_declarations s)
  | Abort (_,s,_) -> collect_internal_signal_declarations s
  | Suspend (_,s,_) -> collect_internal_signal_declarations s
  | While (_,s,_) -> collect_internal_signal_declarations s
  | Send _ | Receive _ -> raise (Internal_error "Collect signals: Cannot get send/receive after re-write!!")


let add_type_and_operator_to_signal t op = function
  | Signal (None,x,y,z) -> Signal (Some {operator=op;data=t},x,y,z)
  | Signal (_,_,_,ln) -> raise (Internal_error ((Reporting.get_line_and_column ln) ^ ": signal already has a type and operator"))
  | _ as s -> 
    let () = Sexplib.Sexp.output_hum stdout (sexp_of_stmt s) in
    raise (Internal_error "Got incorrectly as signal!")


let add_type_and_operator_to_channel t op = function
  | Channel (None,x,y,z) -> Channel (Some {operator=op;data=t},x,y,z)
  | Channel (_,_,_,ln) -> raise (Internal_error ((Reporting.get_line_and_column ln) ^ ": channel already has a type and operator"))
  | _ as s -> 
    let () = Sexplib.Sexp.output_hum stdout (sexp_of_stmt s) in
    raise (Internal_error "Got incorrectly as channel!")

let get_data_type = function
  | Int8s -> "char"
  | Int16s -> "short"
  | Int32s -> "int"

let rec get_simple_data_expr = function
  | Plus (x,y,_) -> get_simple_data_expr x ^ "+" ^ get_simple_data_expr y
  | Minus (x,y,_) -> get_simple_data_expr x ^ "-" ^ get_simple_data_expr y
  | Times (x,y,_) -> get_simple_data_expr x ^ "*" ^ get_simple_data_expr y
  | Div (x,y,_) -> get_simple_data_expr x ^ "/" ^ get_simple_data_expr y
  | Mod (x,y,_) -> get_simple_data_expr x ^ "%" ^ get_simple_data_expr y
  | Rshift (x,y,_) -> get_simple_data_expr x ^ ">>" ^ get_simple_data_expr y
  | Lshift (x,y,_) -> get_simple_data_expr x ^ "<<" ^ get_simple_data_expr y
  | Const (_,y,_) -> y 
  | VarRef (Symbol(x,_),_) -> x
  | Opposite (x,_) -> "-" ^ get_simple_data_expr x
  | DataBrackets (x,_) -> "(" ^ get_simple_data_expr x ^ ")"
  | Cast (x,y,_) -> "(" ^ "(" ^ get_data_type x ^ ")" ^ get_simple_data_expr y ^ ")"
  | _ as s -> let () = Sexplib.Sexp.output_hum stdout (sexp_of_simpleDataExpr s) in
	      let () = print_endline "" in
	      raise (Internal_error "^^^^^^^^^^^^^^^^ currently not supported")

let get_data_expr = function
  | LessThanEqual (x,y,_) -> get_simple_data_expr x ^ "<= " ^ get_simple_data_expr y 
  | LessThan (x,y,_) -> get_simple_data_expr x ^ "<" ^ get_simple_data_expr y
  | GreaterThanEqual (x,y,_) -> get_simple_data_expr x ^ ">=" ^ get_simple_data_expr y
  | GreaterThan(x,y,_) -> get_simple_data_expr x ^ ">" ^ get_simple_data_expr y
  | EqualTo (x,y,_) -> get_simple_data_expr x ^ "==" ^ get_simple_data_expr y
  | NotEqualTo (x,y,_) -> get_simple_data_expr x ^ "!=" ^ get_simple_data_expr y

let get_typedsymbol = function
  | SimTypedSymbol (x,(Symbol(y,_)),_) -> get_data_type x ^ " " ^ y

let get_allsym = function
  | AllSymbol (Symbol (x,_)) -> x
  | AllTypedSymbol x -> get_typedsymbol x
  | AllSignalorChannelSymbol (Symbol(x,_)) -> x

let rec get_expr = function
  | And (x,y,_) -> "(" ^ get_expr x ^ "&&" ^ get_expr y ^ ")"
  | Or (x,y,_) -> "(" ^ get_expr x ^ "||" ^ get_expr y ^ ")"
  | Brackets (x,_) -> "(" ^ get_expr x ^ ")"
  | DataExpr x -> get_data_expr x
  | Not (_,ln) 
  | Esymbol (_,ln)-> raise (Internal_error ((Reporting.get_line_and_column ln) ^ ": non-data type not allowed in here"))

let get_colon_expr = function
  | ColonExpr (x,y,z,_) -> (get_simple_data_expr x, get_simple_data_expr y, get_simple_data_expr z)

let rec get_data_stmt = function
  | RNoop -> ""
  | DataBlock (s,_) -> "{\n" ^ (List.fold_left (^) "" (List.map get_data_stmt s)) ^ "}\n"
  | Assign (x,y,_) -> (get_allsym x) ^ " = " ^ (get_simple_data_expr y) ^ ";\n"
  | CaseDef (x,_) -> get_casedef x
  | For ((Symbol(x,_)),c,s,_,_) -> 
    let (sa,e,st) = get_colon_expr c in
    "for(int "^x^ " = " ^ sa ^ ";" ^ x ^ "<=" ^ e ^ ";" ^ x ^ "=" ^ x ^ "+(" ^ st ^ "))\n"
    ^ get_data_stmt s ^ "\n"
and get_casedef = function
  | Case (x,o,_) -> List.fold_left (^) "" (List.mapi get_clause x) ^ get_otherwise o
and get_clause i = function
  | Clause (x,s,_) -> 
    let st = if i = 0 then "if(" ^(get_expr x)^ ")\n" else "else if(" ^(get_expr x)^ ")\n" in
    st ^ (get_data_stmt s) ^ "\n"
and get_otherwise = function
  | Otherwise (x,_) -> "else{\n" ^ (get_data_stmt x) ^ "}\n"
