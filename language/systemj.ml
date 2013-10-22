(* This is the pure kernel Cgals (seagulls):
   Sun Oct 13 10:23:14 NZDT 2013
   Avinash Malik
   
   The language only supports bounded int types.
*)

(* The current position for error reporting *)
open Sexplib.Std
module List = Batteries.List

let backend = ref ""

let (|>) x f = f x

type line = int
with sexp
type column = int
with sexp


type direction =
| Ack
| Req
with sexp

type location =
| Start
| End
with sexp

type tchan =
| ChanPause of direction * location * string
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
| Esymbol of symbol * (line * column) * tchan option
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

let get_operators = function
  | OpPlus -> " += "
  | OpTimes -> " *= "

type 'a extras = {operator:operators;data:datatype;v:'a}
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
| Pause of string option * (line * column) * tchan option
| Emit of symbol * string option * (line * column)
| Present of expr * stmt * stmt option * (line * column)
| Trap of symbol * stmt * (line * column)
| Signal of string extras option * io option * symbol * (line * column)
| Channel of string extras option * io * symbol * (line * column)
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
| For of symbol * colonDataExpr * dataStmt * string extras option * (line * column)  
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
  | Channel (e,_,(Symbol (x,_)),_) -> [([(x^"_req");(x^"_ack")],e)]
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
  | Signal (x,io,Symbol (s,_),_) -> [(s,x)]
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
  | Signal (x,io,Symbol (s,_),_) -> (match io with Some Input -> [] | _ -> [(s,x)])
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


let add_type_and_operator_to_signal t op init = function
  | Signal (None,x,y,z) -> Signal (Some {operator=op;data=t;v=init},x,y,z)
  | Signal (_,_,_,ln) -> raise (Internal_error ((Reporting.get_line_and_column ln) ^ ": signal already has a type and operator"))
  | _ as s -> 
    let () = Sexplib.Sexp.output_hum stdout (sexp_of_stmt s) in
    raise (Internal_error "Got incorrectly as signal!")


let add_type_and_operator_to_channel t op init = function
  | Channel (None,x,y,z) -> Channel (Some {operator=op;data=t;v=init},x,y,z)
  | Channel (_,_,_,ln) -> raise (Internal_error ((Reporting.get_line_and_column ln) ^ ": channel already has a type and operator"))
  | _ as s -> 
    let () = Sexplib.Sexp.output_hum stdout (sexp_of_stmt s) in
    raise (Internal_error "Got incorrectly as channel!")

let get_data_type = function
  | Int8s -> "unsigned char"
  | Int16s -> "short"
  | Int32s -> "int"

let get_data_type_promela = function
  | Int8s -> "byte"
  | _ as x -> get_data_type x

let rec get_simple_data_expr index asignals = function
  | Plus (x,y,_) -> get_simple_data_expr index asignals x ^ "+" ^ get_simple_data_expr index asignals y
  | Minus (x,y,_) -> get_simple_data_expr index asignals x ^ "-" ^ get_simple_data_expr index asignals y
  | Times (x,y,_) -> get_simple_data_expr index asignals x ^ "*" ^ get_simple_data_expr index asignals y
  | Div (x,y,_) -> get_simple_data_expr index asignals x ^ "/" ^ get_simple_data_expr index asignals y
  | Mod (x,y,_) -> get_simple_data_expr index asignals x ^ "%" ^ get_simple_data_expr index asignals y
  | Rshift (x,y,_) -> get_simple_data_expr index asignals x ^ ">>" ^ get_simple_data_expr index asignals y
  | Lshift (x,y,_) -> get_simple_data_expr index asignals x ^ "<<" ^ get_simple_data_expr index asignals y
  | Const (_,y,_) -> y 
  | VarRef (Symbol(x,_),_) -> x
  | Opposite (x,_) -> "-" ^ get_simple_data_expr index asignals x
  | DataBrackets (x,_) -> "(" ^ get_simple_data_expr index asignals x ^ ")"
  | Cast (x,y,_) -> "(" ^ "(" ^ get_data_type x ^ ")" ^ get_simple_data_expr index asignals y ^ ")"
  | SignalOrChannelRef (Symbol(x,_),ln) as s ->
    let signals = List.split asignals |> (fun (x,_) -> x) in
    if List.exists (fun y -> y = x) signals then 
      if !backend = "promela" then
	"now.CD"^(string_of_int index)^"_"^x^"_val_pre"
      else
	"CD"^(string_of_int index)^"_"^x^"_val_pre"
    else 
      let () = Sexplib.Sexp.output_hum stdout (sexp_of_simpleDataExpr s) in
      let () = print_endline "" in
      raise (Internal_error "^^^^^^^^^^^^^^^^ currently not supported")
  | _ as s -> let () = Sexplib.Sexp.output_hum stdout (sexp_of_simpleDataExpr s) in
  	      let () = print_endline "" in
  	      raise (Internal_error "^^^^^^^^^^^^^^^^ currently not supported")

let get_data_expr index asignals = function
  | LessThanEqual (x,y,_) -> get_simple_data_expr index asignals x ^ "<= " ^ get_simple_data_expr index asignals y 
  | LessThan (x,y,_) -> get_simple_data_expr index asignals x ^ "<" ^ get_simple_data_expr index asignals y
  | GreaterThanEqual (x,y,_) -> get_simple_data_expr index asignals x ^ ">=" ^ get_simple_data_expr index asignals y
  | GreaterThan(x,y,_) -> get_simple_data_expr index asignals x ^ ">" ^ get_simple_data_expr index asignals y
  | EqualTo (x,y,_) -> get_simple_data_expr index asignals x ^ "==" ^ get_simple_data_expr index asignals y
  | NotEqualTo (x,y,_) -> get_simple_data_expr index asignals x ^ "!=" ^ get_simple_data_expr index asignals y

let get_typedsymbol = function
  (* | SimTypedSymbol (x,(Symbol(y,_)),_) -> get_data_type x ^ " " ^ y *)
  | SimTypedSymbol (x,(Symbol(y,_)),_) -> y

let get_allsym index asignals = function
  | AllSymbol (Symbol (x,_)) -> x ^ " = "
  | AllTypedSymbol x -> get_typedsymbol x ^ " = "
  | AllSignalorChannelSymbol (Symbol(x,ln)) as s -> 
    let signals = List.split asignals |> (fun (x,_) -> x) in
    let ops = List.split asignals |> (fun (_,y) -> y) in
    if List.exists (fun y -> y = x) signals then 
      let (x1,_) = List.findi (fun i y -> x = y) signals in
      let ttt = 
	if !backend = "promela" then
	"now.CD"^(string_of_int index)^"_"^x^"_val"
      else
	  "CD"^(string_of_int index)^"_"^x^"_val" in
      ttt ^ (((List.at ops x1) 
		 |> (fun x ->
		   match x with 
		   | Some x -> x.operator 
		   | None -> raise (Internal_error ((Reporting.get_line_and_column ln)^ ": signal has no type and operator"))) 
		 |> get_operators))
    else 
      let () = Sexplib.Sexp.output_hum stdout (sexp_of_allsym s) in
      let () = print_endline "" in
      raise (Internal_error "^^^^^^^^^^^^^^^^ currently not supported")

let rec get_expr index asignals = function
  | And (x,y,_) -> "(" ^ get_expr index asignals x ^ "&&" ^ get_expr index asignals y ^ ")"
  | Or (x,y,_) -> "(" ^ get_expr index asignals x ^ "||" ^ get_expr index asignals y ^ ")"
  | Brackets (x,_) -> "(" ^ get_expr index asignals x ^ ")"
  | DataExpr x -> get_data_expr index asignals x
  | Not (_,ln) 
  | Esymbol (_,ln,_)-> raise (Internal_error ((Reporting.get_line_and_column ln) ^ ": non-data type not allowed in here"))

let get_colon_expr index asignals = function
  | ColonExpr (x,y,z,_) -> (get_simple_data_expr index asignals x, get_simple_data_expr index asignals y, get_simple_data_expr index asignals z)

let rec get_data_stmt index asignals = function
  | RNoop -> ""
  | DataBlock (s,_) -> "{\n" ^ (List.fold_left (^) "" (List.map (get_data_stmt index asignals) s)) ^ "}\n"
  | Assign (x,y,_) -> (get_allsym index asignals x) ^ (get_simple_data_expr index asignals y) ^ ";\n"
  | CaseDef (x,_) -> get_casedef index asignals x
  | For ((Symbol(x,_)),c,s,_,_) -> 
    let (sa,e,st) = get_colon_expr index asignals c in
    "for(int "^x^ " = " ^ sa ^ ";" ^ x ^ "<=" ^ e ^ ";" ^ x ^ "=" ^ x ^ "+(" ^ st ^ "))\n"
    ^ get_data_stmt index asignals s ^ "\n"
and get_casedef index asignals = function
  | Case (x,o,_) -> List.fold_left (^) "" (List.mapi (fun i x -> get_clause i index asignals x) x) ^ get_otherwise index asignals o
and get_clause i index asignals = function
  | Clause (x,s,_) -> 
    let st = if i = 0 then "if(" ^(get_expr index asignals x)^ ")\n" else "else if(" ^(get_expr index asignals x)^ ")\n" in
    st ^ (get_data_stmt index asignals s) ^ "\n"
and get_otherwise index asignals = function
  | Otherwise (x,_) -> "else{\n" ^ (get_data_stmt index asignals x) ^ "}\n"


let rec get_var = function
  | DataBlock (x,_) -> (List.map get_var x) |> List.flatten |> List.sort_unique compare 
  | For (_,_,x,_,_) -> get_var x
  | CaseDef (x,_) -> (get_case_var x) |> List.flatten |> List.sort_unique compare
  | RNoop -> []
  | Assign (x,y,ln) -> 
    (match x with
    | AllTypedSymbol x -> [x]
    | _ -> [])
and get_clause_var = function
  | Clause (_,x,_) -> get_var x
and get_case_var = function
  | Case (l,o,_) -> (List.map get_clause_var l |> List.sort_unique compare) @ (get_o_var o)
and get_o_var = function
  | Otherwise (x,_) -> [get_var x]

let rec get_var_declarations = function
  | Data (x,_) -> get_var x
  | Pause _ | Emit _ | Exit _ | Noop
  | Channel _  | Signal _ -> []
  | Present (_,s,None,_) -> get_var_declarations s
  | Present (_,s,Some x,_) -> get_var_declarations s @ get_var_declarations x
  | Trap (_,s,_) -> get_var_declarations s
  | Block (s,_) 
  | Spar (s,_) -> List.flatten (List.map get_var_declarations s)
  | Abort (_,s,_) -> get_var_declarations s
  | Suspend (_,s,_) -> get_var_declarations s
  | While (_,s,_) -> get_var_declarations s
  | Send _ | Receive _ -> raise (Internal_error "Collect signals: Cannot get send/receive after re-write!!")
