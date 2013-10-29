module L = Batteries.List
module Hashtbl = Batteries.Hashtbl
module Q = Batteries.Queue
module Enum = Batteries.Enum

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration


exception Internal_error of string

let build_data_stmt asignals index from stmt = 
  Systemj.backend := from; 
  let stmt = Systemj.get_data_stmt index asignals
    (match stmt with DataUpdate x -> x 
    | _ as s -> 
      output_hum stdout (sexp_of_proposition s);
      raise (Internal_error "^^^^^^^^^^^^^^^ is not a data-type statment")) in
  match from with
  | "promela" -> "c_code {\n" ^ stmt ^ "};\n"
  | _ -> stmt

let build_data_expr from index asignals expr =
  Systemj.backend := from; 
  let expr = Systemj.get_data_expr index asignals expr in
  match from with
  | "promela" -> "c_expr{" ^ expr ^ "}"
  | _ -> expr

let rec label from tf internal_signals channels index updates isignals asignals = function
  | And (x,y) -> 
    let lv = (label from tf internal_signals channels index updates isignals asignals x)  in
    let rv = (label from tf internal_signals channels index updates isignals asignals y) in
    let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_list sexp_of_string [lv;rv]) ELSE () ENDIF in
    (match (lv,rv) with
    | ("false",_) | (_,"false") -> "false"
    | ("true","true") -> "true"
    | ("true",(_ as s)) | ((_ as s),"true") -> s
    | (_,_) -> "(" ^ lv ^ ")&&(" ^ rv ^ ")")
  | Or (x,y) -> 
    let lv = (label from tf internal_signals channels index updates isignals asignals x)  in
    let rv = (label from tf internal_signals channels index updates isignals asignals y) in
    (match (lv,rv) with
    | ("true",_) | (_,"true") -> "true"
    | ("false","false") -> "false"
    | ("false",(_ as s)) | ((_ as s),"false") -> s
    | (_,_) -> "(" ^ lv ^ ")||(" ^ rv ^ ")")
  | Not (Proposition (x,_)) as s-> 
    let v = (match x with 
      | Expr x ->
	  if (not (L.exists (fun t -> t = x) isignals)) then
	    if x.[0] = '$' then 
	      let () = output_hum stdout (sexp_of_logic s) in
	      raise (Internal_error "^^^^^^^^^^^^ Not emit proposition impossible!")
	    else 
	      if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) 
	      else "(" ^ x ^ ")"
	  else "false"
      | DataExpr x -> build_data_expr from index asignals x
      | DataUpdate x -> raise (Internal_error ("Tried to update data " ^ (to_string_hum (Systemj.sexp_of_dataStmt x)) ^ " on a guard!!"))
      | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!"))
      | Label x -> raise (Internal_error ("Tried to put label " ^ x ^ " on a guard!!"))) in 
    (match v with
    | "false" -> "true"
    | "true" -> "false"
    | _ -> "!("^v^")")
  | Proposition (x,_) -> (match x with 
    | Expr x -> 
	if (not (L.exists (fun t -> t = x) isignals)) then
	  if x.[0] = '$' then "true"
	  else 
	  (* This can only ever happen here! *)
	    (* if not (List.exists (fun (Update t) -> t = x) updates) then *)
	    if not (L.exists (fun t -> t = x) channels) then ("CD"^(string_of_int index)^"_"^x) 
	    else "(" ^ x ^ ")"
	    (* else "true" *)
	else "true"
    | DataExpr x -> build_data_expr from index asignals x
    | DataUpdate x -> raise (Internal_error ("Tried to update data " ^ (to_string_hum (Systemj.sexp_of_dataStmt x)) ^ " on a guard!!"))
    | Update x -> raise (Internal_error ("Tried to update " ^ x ^ " on a guard!!"))
    | Label x -> raise (Internal_error ("Tried to put label " ^ x ^ " on a guard!!"))) 
  | True -> "true"
  | False -> "false"
  | _ as s -> 
    let () = output_hum stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non known proposition type when building transition labels" ))


let rec get_updates index = function
  | And(x,y) 
  | Or(x,y) -> (get_updates index x) @ (get_updates index y)
  | Not (Proposition (x,_)) | Proposition (x,_) as s ->
    (match x with 
    | Expr x -> 
      if x.[0] = '$' then 
	[(Hashtbl.find (L.nth !update_tuple_tbl_ll index) s)]
      else []
    | _ -> [])
  | _ -> []

let get_outgoings o = function
  | ({name=n;incoming=i},guards) ->
    try
      List.iter2 (fun x g -> 
	match Hashtbl.find_option o x with
	| Some ll -> Hashtbl.replace o x ((n,g) :: ll)
	| None -> Hashtbl.add o x [(n,g)]
      ) i guards
    with
    | _ as s -> 
      output_hum stdout (sexp_of_list sexp_of_string i);
      output_hum stdout (sexp_of_list sexp_of_logic guards);
      print_endline ("Node: " ^ n);
      raise s

let rec solve nff q o ret lgn = 
  if not (Q.is_empty q) then
    let element = Q.pop q in
    (* Get all the outgoing nodes from element *)
    (* add these nodes to the queue if they are not already there *)
    let () = IFDEF DEBUG THEN print_endline ("\nElement name: " ^ element.node.name) ELSE () ENDIF in
    let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_list sexp_of_string element.node.incoming) ELSE () ENDIF in
    let oo = (match Hashtbl.find_option o element.node.name with Some x -> x | None -> []) in
    let (oo,_) = L.split oo in
    (* Check if the oo contains names that are already there in the Q *)
    let oo = L.filter (fun x -> not(Enum.exists (fun y -> y.node.name = x) (Q.enum (Q.copy q)))) oo in
    (* Check if these are not already there in ret, because that means they have been visited *)
    let oo = L.filter (fun x -> not(L.exists (fun y -> y.node.name = x) !ret)) oo in
    (* Solve the guard to see if you get a "false" *)
    let oo = List.filter (fun x -> not (List.exists (fun t -> t = x) nff)) oo in
    (* let () = IFDEF DEBUG THEN output_hum stdout (sexp_of_list sexp_of_string oo); print_endline ""; ELSE () ENDIF in *)
    (* Add the remaining elements *)
    let oo = L.map (fun x -> L.find (fun y -> y.node.name = x) lgn) oo in
    (* Add to q *)
    let () = List.iter (fun x -> Q.push x q) oo in
    (* Finally add the element to the return list *)
    ret := element :: !ret;
    (* Call it recursively again *)
    solve nff q o ret lgn
      

(* Reachability using BF traversal *)
let reachability nff lgn = 
  let ret = ref [] in
  let q = Q.create () in
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> get_outgoings o (x.node,x.guards)) lgn in
  (* Added the starting node *)
  let () = Q.push (L.find (fun {tlabels=t} -> (match t with | Proposition (Label x,_) -> x = "st" | _ -> false)) lgn) q in
  let () = solve nff q o ret lgn in
  (* Finally the list is returned *)
  L.sort_unique compare !ret


let rec map7 f a b c d e g i = 
  match (a,b,c,d,e,g,i) with
  | ((h1::t1),(h2::t2),(h3::t3),(h4::t4),(h5::t5),(h6::t6),(h7::t7)) -> 
    (f h1 h2 h3 h4 h5 h6 h7) :: map7 f t1 t2 t3 t4 t5 t6 t7 
  | ([],[],[],[],[],[],[]) -> []
  | _ -> failwith "Lists not of equal length"

let rec map8 f a b c d e g i j = 
  match (a,b,c,d,e,g,i,j) with
  | ((h1::t1),(h2::t2),(h3::t3),(h4::t4),(h5::t5),(h6::t6),(h7::t7),(h8::t8)) -> 
    (f h1 h2 h3 h4 h5 h6 h7 h8) :: map8 f t1 t2 t3 t4 t5 t6 t7 t8
  | ([],[],[],[],[],[],[],[]) -> []
  | _ -> failwith "Lists not of equal length"


let map2i f l1 l2 = 
  let rec ff f i  = function
    | (h::t, h2::t2) -> f i h h2 :: ff f (i+1) (t,t2)
    | ([],[]) -> []
    | _ -> failwith "Lists not of equal length"  in
  ff f 0 (l1,l2)

let get_update_sigs index g =
  let updates = get_updates index g in
  let updates = L.sort_unique compare ((L.map 
    (fun x -> (match x with | Update x ->x | _ ->  raise (Internal_error "Cannot happen!!"))))
    (L.filter (fun x -> (match x with | Update _ ->true | _ -> false)) updates)) in
  updates

let rec eval node updates channels internal_signals signals isignals asignals index outnode = function
  | And (x,y) -> 
      let lv = eval node updates channels internal_signals signals isignals asignals index outnode x in
      let rv = eval node updates channels internal_signals signals isignals asignals index outnode y in
      (match (lv,rv) with
      | (false,_) | (_,false) -> false
      | (true,true) -> true
      | _ -> true
      )
  | Or (x,y) ->
      let lv = eval node updates channels internal_signals signals isignals asignals index outnode x in
      let rv = eval node updates channels internal_signals signals isignals asignals index outnode y in
      (match (lv,rv) with
      | (true,_) | (_,true) -> true
      | (false,false) -> false
      | _ -> true
      )
  | Proposition (x,_) -> 
      (match x with 
      | Expr x -> 
          if x.[0] = '$' || (L.exists (fun y -> x=y )channels)    then 
            true
          else(
            let ii = L.exists (fun y -> x = y ) isignals in
            let up = L.exists (fun y -> x = y ) updates in
            ii || up
          );
      | _ -> true (* Ignoring data atm *)
      )
  | Not (Proposition (x,_)) as s->
      (match x with 
      | Expr x -> 
          if x.[0] = '$' then 
            let () = output_hum Pervasives.stdout (sexp_of_logic s) in
            raise (Internal_error "^^^^^^^^^^^^ Not emit proposition impossible!")
          else(
            let ii = L.exists (fun y -> x = y ) isignals in
            let up = L.for_all (fun y -> x <> y ) updates in
            ii || up
          )
      | _ -> true (* Ignoring data atm *)
      )
  | True -> true
  | False -> false
  | _ as s -> 
    let () = output_hum Pervasives.stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non known proposition type in smt" ))

let rec remove_dollars = function
  | Or (True,True) -> True
  | Or (True,x) -> remove_dollars x
  | Or (x,True) -> remove_dollars x
  | Or (x,y) -> 
      let lval = remove_dollars x in
      let rval = remove_dollars y in
      (match (lval,rval) with
      | (True,True) -> True
      | (True,y) -> y
      | (x,True) -> x
      | (x,y) as t -> Or (x,y))
  | And (True,True) -> True
  | And (True,x) -> remove_dollars x
  | And (x,True) -> remove_dollars x
  | And (x,y) -> 
      let lval = remove_dollars x in
      let rval = remove_dollars y in
      (match (lval,rval) with
      | (True,True) -> True
      | (True,y) -> y
      | (x,True) -> x
      | (x,y) as t -> And (x,y))
  | Proposition (Expr x,_) | Not Proposition (Expr x,_) as s when x.[0] = '$' ->
(*
      print_endline ("SSSS "^x);
      output_hum stdout (sexp_of_proposition (Hashtbl.find (L.nth !update_tuple_tbl_ll 0) s));
      print_endline ("de "^x);
*)
       True
  | _ as t -> t (* Ignoring data *)    

let remove_unreachable index lb channels internal_signals signals isignals asignals =
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> get_outgoings o (x.node,x.guards)) lb in
  let unreachables_all = 
    L.flatten (L.map (fun node ->    
      let updates = L.map (fun x -> get_update_sigs index x) node.guards in
      let olists = match Hashtbl.find_option o node.node.name with | Some (l) -> l | _ -> [] in
      let unreachables = L.map (fun outgoing -> 

        let result = 
          (match node.tlabels with
          | Proposition (Label "st",_) ->
              false
          | _ ->
            L.for_all2 (fun update incoming -> 
              if (incoming <> node.node.name) then(
                not(eval node update channels internal_signals signals isignals asignals index 
                    ((fun (a,b) -> a ) outgoing) ((fun (a,b) -> b) outgoing) ) 
              )
              else(
                true
              )
            ) updates node.node.incoming (* assuming order of updates, incoming and guards are the same *)
          ) in

        if result then
           (fun (a,b) -> Some (a,node.node.name,b)) outgoing (* (node, incoming) node need to rem incoming and its corrs guards *)
        else
          None
       ) olists in
      L.iter (function
        | Some (x,y,g) -> 
            print_endline ("\nunreachables : from "^y^ " to "^x^" with guard");
            output_hum Pervasives.stdout (sexp_of_logic g);
            print_endline ""
        | None -> ()
       ) unreachables;
      unreachables
  ) lb )
  in 

  let unreachables_all = L.filter (fun x -> x <> None) unreachables_all in
  (* First removing edges (incomings) *)
  let () = L.iter (fun n -> 
    L.iter (function Some (remn,remin,uguard) ->
      if(n.node.name = remn) then(
        let ig = L.map2 (fun incoming guard -> 
          print_endline (string_of_bool ((remove_dollars uguard) <> (remove_dollars guard)));
          print_endline (string_of_bool (incoming <> remin));
          if not ((incoming = remin) && ((remove_dollars uguard) = (remove_dollars guard))) then 
            Some (incoming,guard) 
          else( 
            if (n.node.name = "N86") then(
              print_endline ("remn : "^remn^" remin "^remin^" incoming : "^incoming);
              print_endline "N86 removed guard";
              output_hum Pervasives.stdout (sexp_of_logic (remove_dollars uguard));
              print_endline "";
              output_hum Pervasives.stdout (sexp_of_logic (remove_dollars guard));
              print_endline ""
            );
            None 
          )
         
         ) n.node.incoming n.guards in
        let ig = L.filter (function | Some _ -> true | None -> false ) ig in
        let ig = L.map (function | Some ((_) as a) -> a ) ig in
        let ig = L.split ig in
        let () = (fun (i,g) -> n.node.incoming <- i; n.guards <- g) ig in
        ()
      )
    ) unreachables_all
  ) lb in
  (* Second traverse the graph and remove unreachable nodes *)
  let newlb = ref [] in
  let st = L.filter (fun x -> match x.tlabels with | Proposition (Label "st",_) -> true | _ -> false ) lb in
  newlb := (L.hd st) :: !newlb;
  let r = ref true in
  while !r do
    r := L.fold_left (||) false (L.map (fun node ->
      if L.for_all (fun x -> x.node.name <> node.node.name ) !newlb then
          if L.exists (fun x -> L.exists (fun y-> x = y.node.name ) !newlb  ) node.node.incoming then(
            newlb := node :: !newlb;
            true
          )
          else
            false
      else
        false
        ) lb) 
  done;
  !newlb
