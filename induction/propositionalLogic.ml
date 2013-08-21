(* This file implements the inductive semantics described in:


   Embedding imperative synchronous languages in interactive theorem
   provers -- Schnieder, ACSD, 2001
   
   The asynchronous inductive rules are our own -- this is the main
   contribution of this indutive semantics
   
   Thu Aug  1 09:49:37 NZST 2013
   Avinash Malik

*)

module List = Batteries.List

open Sexplib.Sexp
open Sexplib.Std

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
  | Systemj.Pause (_,x) as s -> cnt := !cnt + 1; Systemj.Pause(Some ("L" ^ (string_of_int !cnt)), x)
  | Systemj.Present (e,t,Some el,x) -> Systemj.Present(e,add_labels_and_rewrite cnt t, Some (add_labels_and_rewrite cnt el),x)
  | Systemj.Present (e,t,None,x) -> Systemj.Present(e,add_labels_and_rewrite cnt t, None ,x)
  | Systemj.Block (sl,x) -> Systemj.Block(List.map (add_labels_and_rewrite cnt) (List.rev sl), x)
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
with sexp

type logic = 
| True
| False
| Or of logic * logic
| Not of logic
| And of logic * logic
| Proposition of proposition
| Brackets of logic
| NextTime of logic
with sexp

let rec props = function
  | True | False | Proposition _ as s -> [s]
  | And (x,y) | Or (x,y) -> (props x) @ (props y)
  | Brackets x -> props x
  | NextTime x -> props x
  | Not x -> props x

let rec pos_props = function
  | True | Proposition _ as s -> [s]
  | And (x,y) | Or (x,y) -> (pos_props x) @ (pos_props y)
  | Brackets x -> pos_props x
  | NextTime x -> pos_props x
  | Not (Proposition _) -> []
  | False -> 
    raise (Internal_error "False proposition should never have happened!")
  | _ as s -> 
    let () = output_hum stderr (sexp_of_logic s) in
    raise (Internal_error "Pos_props: ^^^^^^^ cannot solve this formula type!")

let rec neg_props = function
  | True | Proposition _ as s -> []
  | And (x,y) | Or (x,y) -> (neg_props x) @ (neg_props y)
  | Brackets x -> neg_props x
  | NextTime x -> neg_props x
  | Not (Proposition _ as s) -> [s]
  | False -> 
    raise (Internal_error "False proposition should never have happened!")
  | _ as s -> 
    let () = output_hum stderr (sexp_of_logic s) in
    raise (Internal_error "Neg_props: ^^^^^^^ cannot solve this logic formula type!")

let rec push_not = function
  | Not x -> invert_not x
  | True | False as s -> s
  | Brackets x -> Brackets (push_not x)
  | Proposition _ as s -> s
  | NextTime x -> NextTime (push_not x)
  | Or (x,y) -> Or (push_not x, push_not y)
  | And (x,y) -> And (push_not x, push_not y)
and invert_not = function
  | True -> False
  | False -> True
  | Or (x,y) -> push_not (And (Not x, Not y))
  | And (x,y) -> push_not (Or (Not x, Not y))
  | Not x -> push_not x 		(* Not Not x *)
  | _ as s -> Not(push_not s)

let rec collect_labels = function
  | Systemj.Noop | Systemj.Emit _ | Systemj.Signal _ 
  | Systemj.Channel _ | Systemj.Exit _ -> False
  | Systemj.Pause (Some x,_) -> Proposition x
  | Systemj.Block (x,_)  
  | Systemj.Spar (x,_) -> 
    if x = [] then False
    else
      List.reduce (fun x y -> Or (x,y)) (List.map collect_labels x)
  | Systemj.Abort (_,s,_) | Systemj.Suspend (_,s,_)
  | Systemj.While (_,s,_) -> collect_labels s
  | Systemj.Present (_,s,Some el,_) -> Or(collect_labels s, collect_labels el)
  | Systemj.Present (_,s,None,_) -> collect_labels s
  | _ -> raise (Internal_error "Send/Receive after re-writing!")

let rec expr_to_logic = function
  | Systemj.And (x,y,_) -> And(expr_to_logic x, expr_to_logic y)
  | Systemj.Or (x,y,_) -> Or(expr_to_logic x, expr_to_logic y)
  | Systemj.Brackets (x,_) -> Brackets (expr_to_logic x)
  | Systemj.Esymbol (Systemj.Symbol(x,_),_) -> Proposition x

let rec solve_logic = function
  | And (x,y) -> 
    (match (solve_logic x, solve_logic y) with
    | (False,_) | (_,False) -> False
    | (True,True) -> True
    | (x,True) -> x
    | (True,x) -> x
    | (Not (Proposition a), Proposition b) when a = b -> False
    | (Proposition a, Not(Proposition b)) when a = b -> False
    | (NextTime (Not (Proposition a)), NextTime(Proposition b)) when a = b -> False
    | (NextTime (Proposition a), NextTime(Not(Proposition b))) when a = b -> False
    | (x,y) -> And (x,y))
  | Or (x,y) -> 
    (match (solve_logic x, solve_logic y) with
    | (True,_) | (_,True) -> True
    | (False,False) -> False
    | (x,False) -> x
    | (False,x) -> x
    | (Not (Proposition a), Proposition b) when a = b -> True
    | (Proposition a, Not(Proposition b)) when a = b -> True
    | (NextTime (Not (Proposition a)), NextTime(Proposition b)) when a = b -> True
    | (NextTime (Proposition a), NextTime(Not(Proposition b))) when a = b -> True
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
  | Proposition _ as s -> s
  | NextTime x -> 
    (match x with
    | True -> True
    | False -> False
    | _ as s-> NextTime (solve_logic x))

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


(* The function that states if the statements can create a state in the
   big-step semantics *)
let rec enter = function
  | Systemj.Noop -> False
  | Systemj.Emit _ -> False
  | Systemj.Pause (Some x,_) -> NextTime (Proposition x)
  | Systemj.Present (e,t,Some el,_) -> Or(And (NextTime (Not (solve_logic(collect_labels el))), 
					       And (enter t, expr_to_logic e)), 
					  And (NextTime (Not (solve_logic(collect_labels t))),
					       And (enter el, Not (expr_to_logic e))))
  | Systemj.Present (e,t,None,_) -> And (enter t, expr_to_logic e)
  | Systemj.Block (sl,t) as s -> 
    let () = IFDEF SDEBUG THEN let () = output_hum stdout (Systemj.sexp_of_stmt s) in print_endline "" ELSE () ENDIF in
    enter_seq t sl
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
  | h::t -> Or (And(NextTime(Not (solve_logic(collect_labels (Systemj.Block(t,r))))),enter h), 
		And(NextTime (Not (solve_logic(collect_labels h))),
		    And(enter (Systemj.Block(t,r)), solve_logic (inst h)))) 
  | [] -> False
and enter_spar r = function
  | h::t -> 
    Or(Or(And(NextTime (Not (solve_logic(collect_labels h))),
	      And(enter (Systemj.Spar(t,r)),(solve_logic (inst h)))),
	  And(NextTime (Not (solve_logic(collect_labels (Systemj.Spar(t,r))))),
	      And((solve_logic (inst (Systemj.Spar(t,r)))),enter h))),
       And(enter h,enter (Systemj.Spar(t,r))))
  | [] -> False

(* The termination conditions given via inductive big-step semantics *)

(* FIXME: check if semantics of trap are correct *)

let rec term = function
  | Systemj.Noop -> False
  | Systemj.Emit (s,_) -> False
  | Systemj.Pause (Some x,_) -> Proposition x
  | Systemj.Pause (None,lc) -> raise (Internal_error ("Pause without a label: " ^ (Reporting.get_line_and_column lc)))
  | Systemj.Present (e,t,Some el,_) -> And(term t, Not(solve_logic(collect_labels el)))
  | Systemj.Present (e,t,None,_) -> term t
  | Systemj.Block (sl,r) -> term_seq r sl
  | Systemj.Spar (sl,r) -> term_spar r sl
  | Systemj.While (_,s,_) -> False
  | Systemj.Suspend (e,s,_) -> And(Not (expr_to_logic e), term s)
  | Systemj.Abort(e,s,_)  -> And(solve_logic(collect_labels s),Or(expr_to_logic e, term s))
  | Systemj.Trap (e,s,_) -> And(solve_logic(collect_labels s), term s) 	(* You can exit it if the body exits it! *)
  | Systemj.Exit (Systemj.Symbol (s,_),_) -> False
  | Systemj.Signal _ 
  | Systemj.Channel _ -> False
  | _ -> raise (Internal_error "Inst: Cannot get send/receive after rewriting!!")
and term_seq r = function
  | h::t -> Or(And(Not(solve_logic(collect_labels (Systemj.Block(t,r)))),
		   And(term h, solve_logic (inst (Systemj.Block (t,r))))),
	       And(term (Systemj.Block(t,r)),Not(solve_logic(collect_labels h))))
  | [] -> False 			
and term_spar r = function
  | h::t -> Or(Or(And(term h, Not(solve_logic(collect_labels (Systemj.Spar(t,r))))),
		  And(term (Systemj.Spar(t,r)), Not(solve_logic(collect_labels h)))),
	       And(term h, term (Systemj.Spar(t,r))))
  | [] -> False

(* This defines the transitions within a statement *)
let rec move = function
  | Systemj.Noop -> False
  | Systemj.Emit (s,_) -> False
  | Systemj.Pause _ -> False
  | Systemj.Present (e,t,Some el,_) -> 
    Or(And(And(move t,Not(solve_logic(collect_labels el))),NextTime(Not(solve_logic(collect_labels el)))),
       And(And(move el,Not(solve_logic(collect_labels t))),NextTime(Not(solve_logic(collect_labels t)))))
  | Systemj.Present (e,t,None,_) -> False
  | Systemj.Block (sl,r) -> move_seq r sl
  | Systemj.Spar (sl,r) -> move_spar r sl
  | Systemj.While (_,s,_) -> Or(move s,And(term s, solve_logic (enter s)))
  | Systemj.Abort(e,s,_)  -> And(Not(expr_to_logic e),move s)
  | Systemj.Trap (e,s,_) -> move s
  | Systemj.Exit (Systemj.Symbol (s,_),_) -> False
  | Systemj.Signal _ 
  | Systemj.Channel _ -> False
  | Systemj.Suspend (e,s,lc) -> raise (Internal_error ("Suspend current not supported: " ^ (Reporting.get_line_and_column lc)))
  | _ -> raise (Internal_error "Inst: Cannot get send/receive after rewriting!!")
and move_seq r = function
  | h::t -> 
    let fdis = And(move h, And(Not(solve_logic(collect_labels (Systemj.Block(t,r)))),NextTime(Not(solve_logic(collect_labels (Systemj.Block(t,r))))))) in
    let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic (solve_logic fdis)); print_endline"TUTU" ELSE () ENDIF in
    let sdis = And(And(Not(solve_logic(collect_labels h)),NextTime(Not(solve_logic(collect_labels h)))),move (Systemj.Block(t,r))) in
    let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic (solve_logic sdis)); print_endline"TUTU1" ELSE () ENDIF in
    Or(Or(And(move h, And(Not(solve_logic(collect_labels (Systemj.Block(t,r)))),NextTime(Not(solve_logic(collect_labels (Systemj.Block(t,r))))))),
	  And(And(Not(solve_logic(collect_labels h)),NextTime(Not(solve_logic(collect_labels h)))),move (Systemj.Block(t,r)))),
       And(term h,And(NextTime(Not(solve_logic(collect_labels h))),And(Not(solve_logic(collect_labels (Systemj.Block(t,r)))),enter(Systemj.Block(t,r))))))
  | [] -> False
and move_spar r = function
  | h::t -> Or (Or(Or(And(move h,And(Not(solve_logic(collect_labels (Systemj.Spar(t,r)))),NextTime(Not(solve_logic(collect_labels (Systemj.Spar(t,r))))))),
		      And(move (Systemj.Spar(t,r)),And(Not(solve_logic (solve_logic(collect_labels h))),NextTime(Not (solve_logic(collect_labels h)))))),
		   Or(And(move (Systemj.Spar(t,r)), move h),
		      And(move h, And(term (Systemj.Spar(t,r)),NextTime(Not(solve_logic (collect_labels (Systemj.Spar(t,r))))))))),
		And(move (Systemj.Spar(t,r)),And(term h, NextTime(Not (solve_logic (collect_labels h))))))
  | [] -> False

let dltl stmt = 
  let shared = Or(Not(solve_logic (collect_labels stmt)),term stmt) in
  let fdis = And(And(inst stmt, shared),NextTime(Not(solve_logic(collect_labels stmt)))) in
  let sdis = And(shared, enter stmt) in
  let tdis = And(shared, NextTime(Not(solve_logic (collect_labels stmt)))) in
  let fodis = move stmt in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic (solve_logic fodis)); print_endline "<-- FOURTH" ELSE () ENDIF in
  (shared,fdis,sdis,tdis,fodis)

let build_ltl stmt = 
  let shared = Or(Not(solve_logic (collect_labels stmt)),term stmt) in
  let fdis = And(And(inst stmt, shared),NextTime(Not(solve_logic(collect_labels stmt)))) in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic (solve_logic (push_not fdis))); print_endline "<-- FIRST" ELSE () ENDIF in
  let sdis = And(shared, enter stmt) in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic (solve_logic (push_not sdis))); print_endline "<-- SECOND" ELSE () ENDIF in
  let tdis = And(shared, NextTime(Not(solve_logic (collect_labels stmt)))) in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic (solve_logic (push_not tdis))); print_endline "<-- THIRD" ELSE () ENDIF in
  let fdis = move stmt in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic (solve_logic (push_not fdis))); print_endline "<-- FOURTH" ELSE () ENDIF in

  Or(Or(Or(And(shared,And(inst stmt,NextTime(Not(solve_logic(collect_labels stmt))))),
	   And(shared,enter stmt)),
	And(shared,NextTime(Not(solve_logic (collect_labels stmt))))),
     move stmt)

let build_propositional_tree_logic = function
  | Systemj.Apar (x,_) -> 
    List.map solve_logic ((List.map push_not) (List.map build_ltl x))
