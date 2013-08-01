(* This file implements the inductive semantics described in:


   Embedding imperative synchronous languages in interactive theorem
   provers -- Schnieder, ACSD, 2001
   
   The asynchronous inductive rules are our own -- this is the main
   contribution of this indutive semantics
   
   Thu Aug  1 09:49:37 NZST 2013
   Avinash Malik

*)

module List = Batteries.List

exception Internal_error of string

(* TODO: The two functions below need to be completed *)
let rewrite_send = function
  | Systemj.Send _ as s -> s
  | _ -> raise (Internal_error "Tried to rewrite a non-send as send")

let rewrite_receive = function
  | Systemj.Receive _ as s -> s
  | _ -> raise (Internal_error "Tried to rewrite a non-receive as receive")

let rec add_labels_and_rewrite cnt = function
  | Systemj.Pause (_,x) -> cnt := !cnt + 1; Systemj.Pause(Some ("L" ^ (string_of_int !cnt)), x)
  | Systemj.Present (e,t,Some el,x) -> Systemj.Present(e,add_labels_and_rewrite cnt t, Some (add_labels_and_rewrite cnt el),x)
  | Systemj.Present (e,t,None,x) -> Systemj.Present(e,add_labels_and_rewrite cnt t, None ,x)
  | Systemj.Block (sl,x) -> Systemj.Block(List.rev (List.map (add_labels_and_rewrite cnt) sl), x)
  | Systemj.Spar (sl,x) -> Systemj.Spar(List.rev (List.map (add_labels_and_rewrite cnt) sl), x)
  | Systemj.While (ex,s,x) -> Systemj.While(ex,add_labels_and_rewrite cnt s, x)
  | Systemj.Suspend (e,s,x) -> Systemj.Suspend(e,add_labels_and_rewrite cnt s,x)
  | Systemj.Abort(e,s,x) -> Systemj.Abort(e,add_labels_and_rewrite cnt s, x)
  | Systemj.Trap (e,s,x) -> Systemj.Trap(e,add_labels_and_rewrite cnt s, x)
  | Systemj.Noop as s -> s
  | Systemj.Emit _
  | Systemj.Signal _ | Systemj.Exit _ | Systemj.Channel _ as s -> s
  | Systemj.Send _ as s -> rewrite_send s
  | Systemj.Receive _ as s -> rewrite_receive s

let rewrite_ast = function
  | Systemj.Apar (x,s) -> Systemj.Apar (List.map (add_labels_and_rewrite (ref 0)) (List.rev x),s)

type logic = 
| True
| False
| Or of logic * logic
| Not of logic
| And of logic * logic
| Symbol of string
| Brackets of logic


let rec expr_to_logic = function
  | Systemj.And (x,y,_) -> And(expr_to_logic x, expr_to_logic y)
  | Systemj.Or (x,y,_) -> Or(expr_to_logic x, expr_to_logic y)
  | Systemj.Brackets (x,_) -> Brackets (expr_to_logic x)
  | Systemj.Esymbol (Systemj.Symbol(x,_),_) -> Symbol x

let rec solve_logic = function
  | And (x,y) -> 
    (match (solve_logic x, solve_logic y) with
    | (False,_) | (_,False) -> False
    | (True,True) -> True
    | (x,True) -> x
    | (True,x) -> x
    | (x,y) -> And (x,y))
  | Or (x,y) -> 
    (match (solve_logic x, solve_logic y) with
    | (True,_) | (_,True) -> True
    | (False,False) -> False
    | (x,False) -> x
    | (False,x) -> x
    | (x,y) -> Or (x,y))
  | Not x -> 
    (match (solve_logic x) with
    | False -> True
    | True -> False
    | _ as x -> Not x)
  | Brackets x -> 
    (match (solve_logic x) with
    | True -> True
    | False -> False
    | _ as s -> Brackets s)
  | True | False as s -> s
  | Symbol _ as s -> s

(* Function, which states if the statements are instantaneous with
   respect to the logical clock *)

let rec inst = function
  | Systemj.Noop -> True
  | Systemj.Emit (s,_) -> True
  | Systemj.Pause _ -> False
  | Systemj.Present (e,t,Some el,_) -> Or(And(expr_to_logic e, inst t), And(Not (expr_to_logic e), inst el))
  | Systemj.Present (e,t,None,_) -> Or(And(expr_to_logic e, inst t), And(Not (expr_to_logic e), True))
  | Systemj.Block (sl,_) 
  | Systemj.Spar (sl,_) -> 
    if sl = [] then True 
    else List.reduce (fun x y -> And (x,y)) (List.map inst sl)
  | Systemj.While (_,s,_) -> inst s
  | Systemj.Suspend (_,s,_) | Systemj.Abort(_,s,_)  | Systemj.Trap (_,s,_) -> inst s
  | Systemj.Signal _ | Systemj.Exit _ | Systemj.Channel _ -> True
  | _ -> raise (Internal_error "Inst: Cannot get send/receive after rewriting!!")


let rec print_inst = function
  | True -> "(True)"
  | False -> "(False)"
  | Or (x,y) -> "Or("^ print_inst x ^ "," ^ print_inst y ^ ")"
  | And (x,y) -> "And("^ print_inst x ^ "," ^ print_inst y ^ ")"
  | Symbol x -> "Symbol("^ x ^ ")"
  | Brackets x -> "(" ^ print_inst x ^ ")"
  | Not x -> "Not(" ^ print_inst x ^ ")"

type label = string

type enter_logic = 
| EOr of enter_logic * enter_logic
| EAnd of enter_logic * enter_logic
| ENot of enter_logic
| EState of label
| ESymbol of string
| ETrue
| EFalse
| EBrackets of enter_logic
| EInst of logic

let rec expr_to_enter_logic = function
  | Systemj.And (x,y,_) -> EAnd(expr_to_enter_logic x, expr_to_enter_logic y)
  | Systemj.Or (x,y,_) -> EOr(expr_to_enter_logic x, expr_to_enter_logic y)
  | Systemj.Brackets (x,_) -> EBrackets (expr_to_enter_logic x)
  | Systemj.Esymbol (Systemj.Symbol(x,_),_) -> ESymbol x
  | _ -> raise (Internal_error "Cannot get a state type from SystemJ!")

(* The function that states if the statements can create a state in the
   big-step semantics *)
let rec enter = function
  | Systemj.Noop -> EFalse
  | Systemj.Emit _ -> EFalse
  | Systemj.Pause (Some x,_) -> EState x
  | Systemj.Present (e,t,Some el,_) -> EOr(EAnd (enter t, expr_to_enter_logic e), EAnd (enter el, ENot (expr_to_enter_logic e)))
  | Systemj.Present (e,t,None,_) -> EAnd (enter t, expr_to_enter_logic e)
  | Systemj.Block (sl,t) -> enter_seq t sl
  | Systemj.Spar (sl,t) -> enter_spar t sl
  | Systemj.While (_,s,_)
  | Systemj.Suspend (_,s,_) 
  | Systemj.Abort(_,s,_)
  | Systemj.Trap (_,s,_) -> enter s
  | Systemj.Signal _ | Systemj.Exit _ | Systemj.Channel _ -> EFalse
  | Systemj.Pause (None,_) as s -> 
    let () = Systemj.print_stmt s in
    raise (Internal_error "Pause without a label found!!")
  | _ as s -> 
    let () = Systemj.print_stmt s in
    raise (Internal_error "Enter: Cannot get send/receive after rewriting!!")
and enter_seq r = function
  | h::t -> EOr (enter h, EAnd(enter (Systemj.Block(t,r)), EInst (solve_logic (inst h)))) 
  | [] -> EFalse
and enter_spar r = function
  | h::t -> 
    EOr(EOr(EAnd(enter (Systemj.Spar(t,r)),EInst (solve_logic (inst h))),
	    EAnd(EInst (solve_logic (inst (Systemj.Spar(t,r)))),enter h)),
	EAnd(enter h,enter (Systemj.Spar(t,r))))
  | [] -> EFalse

let and_labels = function
  | (EState x, EState y) -> EState (x^y)
  | _ -> raise (Internal_error "Called and_labels without label type")

let rec solve_enter_logic = function
  | EAnd (x,y) -> 
    (match (solve_enter_logic x, solve_enter_logic y) with
    | (EFalse,_) | (_,EFalse) -> EFalse
    | (ETrue, ETrue) -> ETrue
    | (ETrue,x) -> x
    | (x,ETrue) -> x
    | (EState _, EState _) as s -> and_labels s
    | (x,y) -> EAnd (x,y))
  | EOr (x,y) ->
    (match (solve_enter_logic x, solve_enter_logic y) with
    | (ETrue,_) | (_,ETrue) -> ETrue
    | (EFalse,x) -> x
    | (x,EFalse) -> x
    | (x,y) -> EOr(x,y))
  | ENot x ->
    (match (solve_enter_logic x) with
    | EFalse -> ETrue
    | ETrue -> EFalse
    | _ as s -> ENot s)
  | EBrackets x ->
    (match (solve_enter_logic x) with
    | ETrue | EFalse as s -> s
    | _ as s -> EBrackets s)
  | EInst x -> 
    (match (solve_logic x) with
    | True -> ETrue
    | False -> EFalse
    | _ as s -> EInst s)
  | _ as s -> s

let rec print_enter = function
  | ETrue -> "(True)"
  | EFalse -> "(False)"
  | EOr (x,y) -> "Or("^ print_enter x ^ "," ^ print_enter y ^ ")"
  | EAnd (x,y) -> "And("^ print_enter x ^ "," ^ print_enter y ^ ")"
  | ESymbol x -> "Symbol("^ x ^ ")"
  | EBrackets x -> "(" ^ print_enter x ^ ")"
  | EInst x -> "EInst(" ^ print_inst x ^")"
  | EState x -> "(X" ^ x ^ ")"
  | ENot x -> "Not(" ^ print_enter x ^ ")"


(* The termination conditions given via inductive big-step semantics *)

type term_logic =
| TTrue
| TFalse
| TOr of term_logic * term_logic
| TAnd of term_logic * term_logic
| TBrackets of term_logic
| TInst of logic
| TSymbol of string
| TState of label


let build_propositional_tree_logic = function
  | Systemj.Apar (x,_) -> 
    let () = IFDEF DEBUG THEN print_endline "Building INST Tree" ELSE () ENDIF in
    let insts = List.map solve_logic (List.map inst x) in
    let () = IFDEF DEBUG THEN print_endline "Building ENTER Tree" ELSE () ENDIF in
    let enters = List.map solve_enter_logic (List.map enter x) in
    (insts,enters)

