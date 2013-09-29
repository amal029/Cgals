(* This file implements the inductive semantics described in:


   Embedding imperative synchronous languages in interactive theorem
   provers -- Schnieder, ACSD, 2001 and solves a number of logic errors
   in that paper!
   
   
   Thu Aug  1 09:49:37 NZST 2013
   Avinash Malik

*)

module List = Batteries.List
module Hashtbl = Batteries.Hashtbl

open Sexplib.Sexp
open Sexplib.Std

exception Internal_error of string

(* TODO: The two functions below need to be completed *)
let rewrite_send cnt = function
  | Systemj.Send ((Systemj.Symbol (sym,lc1)),lc) -> 
    let ack_sym = Systemj.Symbol ((sym ^ "_ack"),lc1) in
    let req_sym = Systemj.Symbol ((sym ^ "_req"),lc1) in
    cnt := !cnt + 1;
    let a1 = Systemj.Abort (Systemj.Esymbol (ack_sym,lc),
			    Systemj.While(Systemj.True,Systemj.Pause(Some ("$" ^ (string_of_int !cnt)),lc),lc),lc) in
    cnt := !cnt + 1;
    let a2 = Systemj.Abort (Systemj.Not(Systemj.Esymbol (ack_sym,lc),lc),
			    Systemj.While(Systemj.True,
					  Systemj.Block([Systemj.Emit (req_sym,None,lc);
							 Systemj.Pause(Some ("$" ^ (string_of_int !cnt)),lc)],lc),lc),lc) in
    (* Systemj.Block([Systemj.Signal(Some Systemj.Input,ack_sym,lc);Systemj.Signal(Some Systemj.Output,req_sym,lc);a1;a2],lc) *)
    Systemj.Block([Systemj.Signal(Some Systemj.Output,req_sym,lc);a1;a2],lc)
  | _ -> raise (Internal_error "Tried to rewrite a non-send as send")

let rewrite_receive cnt = function
  | Systemj.Receive ((Systemj.Symbol (sym,lc1)),lc) -> 
    let ack_sym = Systemj.Symbol ((sym ^ "_ack"),lc1) in
    let req_sym = Systemj.Symbol ((sym ^ "_req"),lc1) in
    cnt := !cnt + 1;
    let a1 = Systemj.Abort (Systemj.Not(Systemj.Esymbol (req_sym,lc),lc),
			    Systemj.While(Systemj.True,Systemj.Pause(Some ("$" ^ (string_of_int !cnt)),lc),lc),lc) in
    cnt := !cnt + 1;
    let a2 = Systemj.Abort (Systemj.Esymbol (req_sym,lc),
			    Systemj.While(Systemj.True,
					  Systemj.Block([Systemj.Emit (ack_sym,None,lc);
							 Systemj.Pause(Some ("$" ^ (string_of_int !cnt)),lc)],lc),lc),lc) in
    (* Systemj.Block([Systemj.Signal(Some Systemj.Output,ack_sym,lc);Systemj.Signal(Some Systemj.Input,req_sym,lc);a1;a2],lc) *)
    Systemj.Block([Systemj.Signal(Some Systemj.Output,ack_sym,lc);a1;a2],lc)
  | _ -> raise (Internal_error "Tried to rewrite a non-receive as receive")

let rec add_labels_and_rewrite cnt = function
  | Systemj.Pause (None,x) as s -> cnt := !cnt + 1; Systemj.Pause(Some ("$" ^ (string_of_int !cnt)), x)
  | Systemj.Pause _ as s -> s
  | Systemj.Present (e,t,Some el,x) -> 
    let a = add_labels_and_rewrite cnt t in
    let b = add_labels_and_rewrite cnt el in
    Systemj.Present(e,a,Some b,x)
  | Systemj.Present (e,t,None,x) -> Systemj.Present(e,add_labels_and_rewrite cnt t, None ,x)
  | Systemj.Block (sl,x) -> Systemj.Block(List.map (add_labels_and_rewrite cnt) (List.rev sl), x)
  | Systemj.Spar (sl,x) -> Systemj.Spar((List.map (add_labels_and_rewrite cnt) (List.rev sl)), x)
  | Systemj.While (ex,s,x) -> Systemj.While(ex,add_labels_and_rewrite cnt s, x)
  | Systemj.Suspend (e,s,x) -> Systemj.Suspend(e,add_labels_and_rewrite cnt s,x)
  | Systemj.Abort(e,s,x) -> Systemj.Abort(e,add_labels_and_rewrite cnt s, x)
  | Systemj.Trap (e,s,x) -> Systemj.Trap(e,add_labels_and_rewrite cnt s, x)
  | Systemj.Noop as s -> s
  | Systemj.Emit _
  | Systemj.Signal _ | Systemj.Exit _ | Systemj.Channel _ as s -> s
  | Systemj.Send _ as s -> rewrite_send cnt s
  | Systemj.Receive _ as s -> rewrite_receive cnt s

let rec add_unique_identifier_to_emits = function
  | Systemj.Pause _ | Systemj.Noop | Systemj.Signal _
  | Systemj.Channel _ | Systemj.Exit _ as s -> s
  | Systemj.Present (e,t,Some el,x) -> Systemj.Present (e, add_unique_identifier_to_emits t, 
							Some (add_unique_identifier_to_emits el), x)
  | Systemj.Present(e,a,None,x) -> Systemj.Present (e, add_unique_identifier_to_emits a,None, x)
  | Systemj.Block (sl,x) -> Systemj.Block(List.map add_unique_identifier_to_emits sl, x)
  | Systemj.Spar (sl,x) -> Systemj.Spar(List.map add_unique_identifier_to_emits sl, x)
  | Systemj.While (ex,s,x) -> Systemj.While(ex,add_unique_identifier_to_emits s, x)
  | Systemj.Suspend (e,s,x) -> Systemj.Suspend(e,add_unique_identifier_to_emits s,x)
  | Systemj.Abort(e,s,x) -> Systemj.Abort(e,add_unique_identifier_to_emits s, x)
  | Systemj.Trap (e,s,x) -> Systemj.Trap(e,add_unique_identifier_to_emits s, x)
  | Systemj.Emit (x,None,lc) -> Systemj.Emit (x,Some (string_of_int (BatPervasives.unique())),lc)
  | _ as s -> 
    let () = output_hum stdout (Systemj.sexp_of_stmt s) in
    let () = print_endline "" in
    raise (Internal_error ("^^^^^^^^^^^^^^^^^^" ^ " should not happen!!"))


let rewrite_ast = function
  | Systemj.Apar (x,s) -> 
    Systemj.Apar (List.map add_unique_identifier_to_emits (List.map (add_labels_and_rewrite (ref 0)) (List.rev x)),s)

type proposition = 
| Label of string
| Expr of string
| Update of string
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

type update_tuple = logic * proposition
with sexp

let rec props = function
  | True | False | Proposition _ as s -> [s]
  | And (x,y) | Or (x,y) -> (props x) @ (props y)
  | Brackets x -> props x
  | NextTime x -> props x
  | Not x -> props x

let rec push_not = function
  | Not x -> invert_not x
  | True | False as s -> s
  | Brackets x -> push_not x
  | Proposition _ as s -> s
  | NextTime x -> NextTime (push_not x)
  | Or (x,y) -> Or (push_not x, push_not y)
  | And (x,y) -> And (push_not x, push_not y)
and invert_not = function
  | True -> False
  | False -> True
  | Or (x,y) -> push_not (And (Not x, Not y))
  | And (x,y) -> push_not (Or (Not x, Not y))
  | Not x -> push_not x 
  | Brackets x -> push_not (Not x)
  | NextTime x -> push_not (NextTime (Not x))
  | _ as s -> Not s

let rec collect_labels = function
  | Systemj.Noop | Systemj.Emit _ | Systemj.Signal _ 
  | Systemj.Channel _ | Systemj.Exit _ -> False
  | Systemj.Pause (Some x,_) -> Proposition (Label x)
  | Systemj.Block (x,_)  
  | Systemj.Spar (x,_) -> 
    if x = [] then False
    else
      List.reduce (fun x y -> Or (x,y)) (List.map collect_labels x)
  | Systemj.Abort (_,s,_) | Systemj.Suspend (_,s,_) | Systemj.Trap(_,s,_)
  | Systemj.While (_,s,_) -> collect_labels s
  | Systemj.Present (_,s,Some el,_) -> Or(collect_labels s, collect_labels el)
  | Systemj.Present (_,s,None,_) -> collect_labels s
  | _ -> raise (Internal_error "Send/Receive after re-writing!")

let rec expr_to_logic = function
  | Systemj.And (x,y,_) -> And(expr_to_logic x, expr_to_logic y)
  | Systemj.Or (x,y,_) -> Or(expr_to_logic x, expr_to_logic y)
  | Systemj.Brackets (x,_) -> Brackets (expr_to_logic x)
  | Systemj.Esymbol (Systemj.Symbol(x,_),_) -> Proposition (Expr x)
  | Systemj.Not (x,_) -> Not(expr_to_logic x)

let rec solve_logic = function
  | And (x,y) -> 
    (match (solve_logic x, solve_logic y) with
    | (False,_) | (_,False) -> False
    | (True,True) -> True
    | (x,True)
    | (True,x) -> x
    | ((Proposition a), Proposition b) when a = b -> Proposition a
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
    | ((Proposition a), Proposition b) when a = b -> Proposition a
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
  | NextTime x when x = True -> True
  | NextTime x -> NextTime (solve_logic x)

(* Function, which states if the statements are instantaneous with
   respect to the logical clock *)
let update_tuple_tbl = Hashtbl.create 1000
let update_tuple_tbl_ll = ref []
let update_tuple_proposition = Hashtbl.create 1000
let update_tuple_proposition_ll = ref []

let rec inst = function
  | Systemj.Noop -> True
  (* Special change, adding data to the system!! *)
  | Systemj.Emit (s,Some uniq,_) -> 
    let key = Proposition (Expr ("$" ^ uniq)) in
    let () = Hashtbl.add update_tuple_tbl key (Update (match s with | Systemj.Symbol (s,_) -> s)) in
    let exprr = (Proposition (Expr (match s with Systemj.Symbol (s,_)->s))) in
    let () = Hashtbl.add update_tuple_proposition key exprr in
    NextTime key
  | Systemj.Emit (s,None,_) as t -> 
    let () = output_hum stdout (Systemj.sexp_of_stmt t) in
    raise (Internal_error "Emit stmt without a unique identifier cannot be initialized for data propositions")
  | Systemj.Pause _ -> False
  | Systemj.Present (e,t,Some el,_) -> Or(And(NextTime (expr_to_logic e), inst t), And(NextTime (Not (expr_to_logic e)), inst el))
  (* FIXME: Check if this is correct logic? *)
  (* | Systemj.Present (e,t,None,_) -> And(NextTime (expr_to_logic e), inst t) *)
  | Systemj.Present (e,t,None,_) -> Or(And(NextTime (expr_to_logic e), inst t), And(NextTime (Not (expr_to_logic e)), True))
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
  | Systemj.Pause (Some x,_) -> NextTime (Proposition (Label x))
  | Systemj.Present (e,t,Some el,_) -> Or(And (NextTime (Not ((collect_labels el))), 
					       And (enter t, NextTime (expr_to_logic e))), 
					  And (NextTime (Not ((collect_labels t))),
					       And (enter el, NextTime (Not (expr_to_logic e)))))
  | Systemj.Present (e,t,None,_) -> And (enter t, NextTime (expr_to_logic e))
  | Systemj.Block (sl,t) as s -> enter_seq t sl
  | Systemj.Spar (sl,t) -> enter_spar t sl
  | Systemj.While (_,s,_)
  | Systemj.Suspend (_,s,_) 
  | Systemj.Abort(_,s,_)
  | Systemj.Trap (_,s,_) -> enter s
  | Systemj.Signal _ | Systemj.Exit _ | Systemj.Channel _ -> False
  | Systemj.Pause (None,_) as s -> 
    let () = output_hum stdout (Systemj.sexp_of_stmt s) in
    raise (Internal_error "Pause without a label found!!")
  | _ as s -> 
    let () = output_hum stdout (Systemj.sexp_of_stmt s) in
    raise (Internal_error "Enter: Cannot get send/receive after rewriting!!")
and enter_seq r = function
  | h::t -> Or (And(NextTime(Not ((collect_labels (Systemj.Block(t,r))))),enter h), 
		And(NextTime (Not ((collect_labels h))),
		    And(enter (Systemj.Block(t,r)),  (inst h)))) 
  | [] -> False
and enter_spar r = function
  | h::t -> 
    Or(Or(And(NextTime (Not ((collect_labels h))),
	      And(enter (Systemj.Spar(t,r)),( (inst h)))),
	  And(NextTime (Not ((collect_labels (Systemj.Spar(t,r))))),
	      And(( (inst (Systemj.Spar(t,r)))),enter h))),
       And(enter h,enter (Systemj.Spar(t,r))))
  | [] -> False

(* The termination conditions given via inductive big-step semantics *)

(* FIXME: check if semantics of trap are correct *)

let rec term = function
  | Systemj.Noop -> False
  | Systemj.Emit _ -> False
  | Systemj.Pause (Some x,_) -> Proposition (Label x)
  | Systemj.Pause (None,lc) -> raise (Internal_error ("Pause without a label: " ^ (Reporting.get_line_and_column lc)))
  | Systemj.Present (e,t,Some el,_) -> Or(And(And(term t, Not((collect_labels el))),NextTime(expr_to_logic e)),
					  And(term el, Not( (collect_labels t))))
  | Systemj.Present (e,t,None,_) -> term t
  | Systemj.Block (sl,r) -> term_seq r sl
  | Systemj.Spar (sl,r) -> term_spar r sl
  | Systemj.While (_,s,_) -> False
  | Systemj.Suspend (e,s,_) -> And(NextTime(Not (expr_to_logic e)), term s)
  | Systemj.Abort(e,s,_)  -> And((collect_labels s),Or(NextTime (expr_to_logic e), term s))
  | Systemj.Trap (e,s,_) -> And((collect_labels s), term s) 	(* You can exit it if the body exits it! *)
  | Systemj.Exit (Systemj.Symbol (s,_),_) -> False
  | Systemj.Signal _ 
  | Systemj.Channel _ -> False
  | _ -> raise (Internal_error "Inst: Cannot get send/receive after rewriting!!")
and term_seq r = function
  | h::t -> Or(And(Not((collect_labels (Systemj.Block(t,r)))),
		   And(term h,  (inst (Systemj.Block (t,r))))),
	       And(term (Systemj.Block(t,r)),Not((collect_labels h))))
  | [] -> False 			
and term_spar r = function
  | h::t -> Or(Or(And(term h, Not((collect_labels (Systemj.Spar(t,r))))),
		  And(term (Systemj.Spar(t,r)), Not((collect_labels h)))),
	       And(term h, term (Systemj.Spar(t,r))))
  | [] -> False

(* Use (a /\ b) \/ (~b /\ ~a) version of the <=> law, because it will result
   in smaller graph *)
let rec stutters = function
  | Systemj.Noop | Systemj.Emit _ | Systemj.Signal _ 
  | Systemj.Channel _ | Systemj.Exit _ -> True
  | Systemj.Pause (Some x,_) -> Or(And(Proposition (Label x), NextTime (Proposition (Label x))), 
				   And(Not (Proposition (Label x)), NextTime (Not(Proposition (Label x)))))
  | Systemj.Block (x,_)  
  | Systemj.Spar (x,_) -> 
    if x = [] then True
    else
      List.reduce (fun x y -> And (x,y)) (List.map stutters x)
  | Systemj.Abort (_,s,_) | Systemj.Suspend (_,s,_) | Systemj.Trap(_,s,_)
  | Systemj.While (_,s,_) -> stutters s
  | Systemj.Present (_,s,Some el,_) -> And(stutters s, stutters el)
  | Systemj.Present (_,s,None,_) -> stutters s
  | _ -> raise (Internal_error "Send/Receive after re-writing!")


(* This defines the transitions within a statement *)
let rec move = function
  | Systemj.Noop -> False
  | Systemj.Emit _ -> False
  | Systemj.Pause _ -> False
  | Systemj.Present (e,t,Some el,_) -> 
    Or(And(And(move t,Not((collect_labels el))),NextTime(Not((collect_labels el)))),
       And(And(move el,Not((collect_labels t))),NextTime(Not((collect_labels t)))))
  | Systemj.Present (e,t,None,_) -> move t
  | Systemj.Block (sl,r) -> move_seq r sl
  | Systemj.Spar (sl,r) -> move_spar r sl
  | Systemj.While (_,s,_) -> Or(move s,And(term s,  (enter s)))
  | Systemj.Abort(e,s,_)  -> And(NextTime (Not(expr_to_logic e)),move s)
  | Systemj.Trap (e,s,_) -> move s
  | Systemj.Exit (Systemj.Symbol (s,_),_) -> False
  | Systemj.Signal _ 
  | Systemj.Channel _ -> False
  | Systemj.Suspend (e,s,lc) -> 
    let sigma =  (expr_to_logic e) in
    let inS = ( (collect_labels s)) in
    let mS = ( (move s)) in
    let stutterS =  (stutters s) in
    (Or(And(And(NextTime sigma,inS),stutterS),And(NextTime (Not sigma), mS)))
  | _ -> raise (Internal_error "Inst: Cannot get send/receive after rewriting!!")
and move_seq r = function
  | h::t -> 
    (* let fdis = And(move h, And(Not((collect_labels (Systemj.Block(t,r)))),NextTime(Not((collect_labels (Systemj.Block(t,r))))))) in *)
    (* let sdis = And(And(Not((collect_labels h)),NextTime(Not((collect_labels h)))),move (Systemj.Block(t,r))) in *)
    Or(Or(And(move h, And(Not((collect_labels (Systemj.Block(t,r)))),NextTime(Not((collect_labels (Systemj.Block(t,r))))))),
	  And(And(Not((collect_labels h)),NextTime(Not((collect_labels h)))),move (Systemj.Block(t,r)))),
       And(term h,And(NextTime(Not((collect_labels h))),And(Not((collect_labels (Systemj.Block(t,r)))),enter(Systemj.Block(t,r))))))
  | [] -> False
and move_spar r = function
  | h::t -> Or (Or(Or(And(move h,And(Not((collect_labels (Systemj.Spar(t,r)))),NextTime(Not((collect_labels (Systemj.Spar(t,r))))))),
		      And(move (Systemj.Spar(t,r)),And(Not((collect_labels h)),NextTime(Not ((collect_labels h)))))),
		   Or(And(move (Systemj.Spar(t,r)), move h),
		      And(move h, And(term (Systemj.Spar(t,r)),NextTime(Not( (collect_labels (Systemj.Spar(t,r))))))))),
		And(move (Systemj.Spar(t,r)),And(term h, NextTime(Not ( (collect_labels h))))))
  | [] -> False

let build_ltl stmt = 
  let shared = Or(Not( (collect_labels stmt)),term stmt) in
  let fdis = And(And(inst stmt, Proposition (Label "st")),NextTime(Not((collect_labels stmt)))) in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic ( solve_logic (push_not fdis))); print_endline "<-- FIRST" ELSE () ENDIF in
  let sdis = And(Proposition (Label "st"), enter stmt) in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic ( solve_logic (push_not sdis))); print_endline "<-- SECOND" ELSE () ENDIF in
  let tdis = And(Not(Proposition (Label "st")), NextTime(Not( (collect_labels stmt)))) in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic ( solve_logic (push_not tdis))); print_endline "<-- THIRD" ELSE () ENDIF in
  let fdis = move stmt in
  let () = IFDEF PDEBUG THEN output_hum stdout (sexp_of_logic ( solve_logic (push_not fdis))); print_endline "<-- FOURTH" ELSE () ENDIF in

  Or(Or(Or(And(Proposition (Label "st"),And(inst stmt,NextTime(Not((collect_labels stmt))))),
	   And(Proposition (Label "st"),enter stmt)),
	And(Not(Proposition (Label "st")),NextTime(Not( (collect_labels stmt))))),
     move stmt)


let build_propositional_tree_logic = function
  | Systemj.Apar (x,_) -> 
    List.map (fun x -> 
      let control_logic =  solve_logic (push_not (build_ltl x)) in
      update_tuple_tbl_ll := !update_tuple_tbl_ll @ [Hashtbl.copy update_tuple_tbl];
      update_tuple_proposition_ll := !update_tuple_proposition_ll @ [Hashtbl.copy update_tuple_proposition];
      let () = IFDEF PDEBUG THEN print_int (List.length !update_tuple_tbl_ll); print_endline "-- LEN" ELSE () ENDIF in
      let () = Hashtbl.clear update_tuple_tbl in
      let () = Hashtbl.clear update_tuple_proposition in
      control_logic) x

let rec string_of_logic = function
  | Or (x,y) -> (string_of_logic x) ^ "_or_" ^ (string_of_logic y)
  | Not x -> "_not_" ^ (string_of_logic x)
  | And (x,y) -> (string_of_logic x) ^ "_and_" ^ (string_of_logic y)
  | Proposition x -> (match x with | Label x -> x | Expr x -> x 
    | Update _ -> raise (Internal_error "string_of_logic: Update should not occur here!!"))
  | Brackets x -> (string_of_logic x)
  | True -> "True"
  | _ as s -> 
    output_hum stdout (sexp_of_logic s);
    raise (Internal_error "This logic type cannot happen at Uppaal generation stage")
