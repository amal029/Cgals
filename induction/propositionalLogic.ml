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
let rewrite_send cnt = function
  | Systemj.Send (sym,lc) -> cnt := !cnt + 1; 
    Systemj.Abort (Systemj.Esymbol (sym,lc),
		   Systemj.While(Systemj.True,Systemj.Pause(Some ("L" ^ (string_of_int !cnt)),lc),lc),lc)
  | _ -> raise (Internal_error "Tried to rewrite a non-send as send")

let rewrite_receive cnt = function
  | Systemj.Receive (sym,lc) -> 
    cnt := !cnt + 1;
    Systemj.Abort (Systemj.Esymbol (sym,lc),
		   Systemj.While(Systemj.True,Systemj.Pause(None,lc),lc),lc)
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
  | Systemj.Send _ as s -> rewrite_send cnt s
  | Systemj.Receive _ as s -> rewrite_receive cnt s

let rewrite_ast = function
  | Systemj.Apar (x,s) -> Systemj.Apar (List.map (add_labels_and_rewrite (ref 0)) (List.rev x),s)

type proposition = string

type logic = 
| True
| False
| Or of logic * logic
| Not of logic
| And of logic * logic
| Proposition of proposition
| Brackets of logic
| NextTime of proposition

let rec collect_labels = function
  | Noop | Emit _ | Signal _ 
  | Channel _ | Exit _ -> False
  | Pause (Some x,) -> Proposition x
  | Block (x,_)  
  | Spar (s,_) -> List.reduce (fun x y -> Or (x,y)) (List.map collect_labels x)
  | Abort (_,s,_) | Suspend (_,s,_) |
  | While (_,s,_) -> collect_labels s
  | _ -> raise (Internal_error "Send/Receive after re-writing!")

let rec expr_to_logic = function
  | Systemj.And (x,y,_) -> And(expr_to_logic x, expr_to_logic y)
  | Systemj.Or (x,y,_) -> Or(expr_to_logic x, expr_to_logic y)
  | Systemj.Brackets (x,_) -> Brackets (expr_to_logic x)
  | Systemj.Esymbol (Systemj.Symbol(x,_),_) -> Porposition x

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
  | Porposition _ as s -> s
  | NextTime _ as s -> s

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


let rec print = function
  | True -> "(True)"
  | False -> "(False)"
  | Or (x,y) -> "Or("^ print x ^ "," ^ print y ^ ")"
  | And (x,y) -> "And("^ print x ^ "," ^ print y ^ ")"
  | Proposition x -> "Proposition("^ x ^ ")"
  | Brackets x -> "(" ^ print x ^ ")"
  | Not x -> "Not(" ^ print x ^ ")"


(* The function that states if the statements can create a state in the
   big-step semantics *)
let rec enter = function
  | Systemj.Noop -> False
  | Systemj.Emit _ -> False
  | Systemj.Pause (Some x,_) -> NextTime x
  | Systemj.Present (e,t,Some el,_) -> Or(And (NextTime (Not (collect_labels el)), 
					       And (enter t, expr_to_logic e)), 
					  And (NextTime (Not (collect_labels t)),
					       And (enter el, Not (expr_to_logic e))))
  | Systemj.Present (e,t,None,_) -> And (enter t, expr_to_logic e)
  | Systemj.Block (sl,t) -> enter_seq t sl
  | Systemj.Spar (sl,t) -> enter_spar t sl
  | Systemj.While (_,s,_)
  | Systemj.Suspend (_,s,_) 
  | Systemj.Abort(_,s,_)
  | Systemj.Trap (_,s,_) -> enter s
  | Systemj.Signal _ | Systemj.Exit _ | Systemj.Channel _ -> False
  | Systemj.Pause (None,_) as s -> 
    let () = Systemj.print_stmt s in
    raise (Internal_error "Pause without a label found!!")
  | _ as s -> 
    let () = Systemj.print_stmt s in
    raise (Internal_error "Enter: Cannot get send/receive after rewriting!!")
and enter_seq r = function
  | h::t -> Or (And(NextTime(Not (collect_labels Systemj.Block(t,r))),enter h), 
		And(NextTime (Not (collect_labels h)),
		    And(enter (Systemj.Block(t,r)), solve_logic (inst h)))) 
  | [] -> False
and enter_spar r = function
  | h::t -> 
    Or(Or(And(NextTime (Not (collect_labels h)),
	      And(enter (Systemj.Spar(t,r)),(solve_logic (inst h)))),
	  And(NextTime (Not (collect_labels Systemj.Spar(t,r))),
	      And((solve_logic (inst (Systemj.Spar(t,r)))),enter h))),
       And(enter h,enter (Systemj.Spar(t,r))))
  | [] -> False

(* The termination conditions given via inductive big-step semantics *)

(* FIXME: check if semantics of trap are correct *)

let rec term = function
  | Systemj.Noop -> False
  | Systemj.Emit (s,_) -> False
  | Systemj.Pause (Some (Systemj.Symbol x, _)) -> Proposition x
  | Systemj.Pause (None,lc) -> raise (Internal_error "Pause without a label: " ^ (Reporting.get_line_and_column lc))
  | Systemj.Present (e,t,Some el,_) -> And(term t, Not(collect_labels el))
  | Systemj.Present (e,t,None,_) -> term t
  | Systemj.Block (sl,r) -> term_seq r sl
  | Systemj.Spar (sl,r) -> term_spar r sl
  | Systemj.While (_,s,_) -> False
  | Systemj.Suspend (e,s,_) -> And(Not (expr_to_logic e), term s)
  | Systemj.Abort(e,s,_)  -> And(collect_labels s,Or(expr_to_logic e, term s))
  | Systemj.Trap (e,s,_) -> And(collect_labels s, term s) 	(* You can exit it if the body exits it! *)
  | Systemj.Exit (Systemj.Symbol s,_) -> False
  | Systemj.Signal _ 
  | Systemj.Channel _ -> False
  | _ -> raise (Internal_error "Inst: Cannot get send/receive after rewriting!!")
and term_seq r = function
  | h::t -> Or(And(Not(collect_labels (Systemj.Block(t,r))),
		   And(term h, solve_logic (inst Systemj.Block (t,r)))),
	       And(term (Systemj.Block(t,r)),Not(collect_labels h)))
  | [] -> False 			
and term_spar r = function
  | h::t -> Or(And(term h, Not(collect_labels (Systemj.Spar(t,r)))),
	       And(term (Systemj.Spar(t,r)), Not(collect_labels h)),
	       And(term h, term (Systemj.Spar(t,r))))
  | [] -> False

(* This defines the transitions within a statement *)
let rec move = function
  | Systemj.Noop -> False
  | Systemj.Emit (s,_) -> False
  | Systemj.Pause _ -> False
  | Systemj.Present (e,t,Some el,_) -> 
    Or(And(And(move t,Not(collect_labels el)),NextTime(Not(collect_labels el))),
       And(And(move el,Not(collect_labels t)),NextTime(Not(collect_labels t))))
  | Systemj.Present (e,t,None,_) -> False
  | Systemj.Block (sl,r) -> move_seq r sl
  | Systemj.Spar (sl,r) -> move_spar r sl
  | Systemj.While (_,s,_) -> Or(move s,And(term s, solve_logic (enter s)))
  | Systemj.Abort(e,s,_)  -> And(Not(expr_to_logic e),move s)
  | Systemj.Trap (e,s,_) -> move s
  | Systemj.Exit (Systemj.Symbol s,_) -> False
  | Systemj.Signal _ 
  | Systemj.Channel _ -> False
  | Systemj.Suspend (e,s,lc) -> raise (Internal_error ("Suspend current not supported: " ^ (Reporting.get_line_and_column lc)))
  | _ -> raise (Internal_error "Inst: Cannot get send/receive after rewriting!!")
and move_seq r = function
  | h::t -> Or(And(move h, And(Not(collect_labels (Systemj.Block(t,r))),NextTime(Not(collect_labels (Systemj.Block(t,r)))))),
	       And(And(Not(collect_labels h),NextTime(Not(collect_labels h))),move (Systemj.Block(t,r))),
	       And(term h,And(NextTime(Not(collect_labels h)),And(Not(collect_labels (Systemj.Block(t,r))),enter(Systemj.Block(t,r))))))
  | [] -> False
and move_spar r = function
  | h::t -> Or (And(move h,And(Not(collect_labels (Systemj.Spar(r,t))),NextTime(Not(collect_labels (Systemj.Spar(t,r))),NextTime()))),
		And(move (Systemj.Spar(t,r)),And(Not(collect_labels h),NextTime(Not (collect_labels h)))),
		And(move (Systemj.Spar(t,r)), move h),
		And(move h, And(term (Systemj.Spar(t,r)),NextTime(Not(collect_labels (Systemj.Spar(t,r)))))),
		And(move (Systemj.Spar(t,r)),And(term h, NextTime(Not(collect_labels h)))))
  | [] -> False

let build_propositional_tree_logic = function
  | Systemj.Apar (x,_) -> 
    let () = IFDEF DEBUG THEN print_endline "Building INST Tree" ELSE () ENDIF in
    let insts = List.map solve_logic (List.map inst x) in
    let () = IFDEF DEBUG THEN print_endline "Building ENTER Tree" ELSE () ENDIF in
    let enters = List.map solve_logic (List.map enter x) in
    (insts,enters)

