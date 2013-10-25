module List = Batteries.List 
module SS = Sexplib.Sexp 
module SSL = Sexplib.Std 
module String = Batteries.String 
module Hashtbl = Batteries.Hashtbl
module Enum = Batteries.Enum
open Systemj
open Pretty 
open TableauBuchiAutomataGeneration 
open PropositionalLogic 
let (++) = append 
let (>>) x f = f x
let wctt_opt = ref (Hashtbl.create 10)
let wcrt_opt = ref (Hashtbl.create 10)

exception Internal_error of string

let print_states lba = let ss = List.reduce (^) (List.mapi (fun y f ->  
  (List.reduce (^) (List.map (fun k -> "(declare-fun CD"^(string_of_int y)^"_"^k.node.name^" () Int)\n") f) )) lba) in ss 

let string_of_direction = function
  | Ack -> "Ack"
  | Req -> "Req"

let string_of_location = function
  | Start -> "Start"
  | End -> "End"

let string_of_tchan = function
  | ChanPause (a,b,c) -> ((string_of_direction a)^(string_of_location b)^c)

let print_sequentiality lba =
  let adecl = ref [] in
  let ors = ref [] in
  let ss = ref "" in
  ss := List.reduce (^) (List.mapi (fun y f ->
    let doc = List.fold_left (^) ("(assert (and " ) 
      (List.map (fun x -> 
        if (x.tlabels = Proposition (Label "st",[None])) then
          ("(>= CD"^(string_of_int y)^"_"^x.node.name^" 0) ")
        else
          List.reduce (^) (List.map (fun k -> 
            let str = ref "" in
            (if List.exists (fun tt -> tt.node.name = k) f then(
              (* Insering micro states *)
              x.node.incoming_chan <- (List.unique x.node.incoming_chan);
              (if (List.is_empty x.node.incoming_chan = false)  then
                  let ors2 = ref [] in
                  let () = List.iter (fun z -> 
                    (match z with
                    | Proposition (Label (s),[Some ((ChanPause (a,b,c)) as p)]) ->
                      let microst = ("CD"^(string_of_int y)^"_"^x.node.name^"-"^(string_of_tchan p)) in
		      (*                         let tutu = ("(declare-fun "^microst^" () Int)") in *)
                      adecl := microst :: !adecl;
                      let multdep = ref [] in
                      List.iter(fun u ->
                        (* micrsteps depends on the previous state on the same CD *)
                        let wctt1 = (match Hashtbl.find_option !wctt_opt y with | Some (t) -> t | None -> "1") in
                        str := (!str^" (>= "^microst^" (+ CD"^(string_of_int y)^"_"^k^" "^wctt1^")) ");
                        (match (p, (match u with | (inchan,Systemj.ChanPause (g,h,l)) -> (inchan,g,h,l) )) with
                        | (ChanPause (Ack,Start,cn) (*("$AckStart",cn)*), (inchan,Systemj.Req,Systemj.Start,l)) 
                        | (ChanPause (Ack,End,cn) (*("$AckEnd",cn)*), (inchan,Systemj.Req,Systemj.End,l))
                        | (ChanPause (Req,End,cn) (*("$ReqEnd",cn)*), (inchan,Systemj.Ack,Systemj.Start,l)) 
                            when (match String.split cn "_" with | (x,_) -> x) = (match String.split l "_" with | (x,_) -> x) -> 
                          (* macrostate can finish when any of one of deps finish for the same microst  *)
                          let cdnum = int_of_string (String.lchop ~n:2 (List.at (String.nsplit inchan "_") 0)) in
                          let wctt1 = (match Hashtbl.find_option !wctt_opt cdnum with | Some (t) -> t | None -> "1") in
                          multdep := (" (>= "^microst^" (+ "^inchan^" "^wctt1^")) ") :: !multdep;
                        | _ -> ()
                        );
                        ors2 := ("(= CD"^(string_of_int y)^"_"^x.node.name^" "^microst^") ") :: !ors2;
                      ) x.node.incoming_chan;
                      str := (!str ^ (match !multdep with
                      | [] -> ""
                      | _::_ -> 
                        let mys = List.fold_left (^) ("(and ") !multdep in
                        let mys = (mys ^ " )") in
                        mys))

                    | _ -> () )
                  ) x.tls in
                  if(not (List.is_empty !ors2)) then
                    ors := (((List.fold_left (^) ("(assert (or ") !ors2) ^ "))\n")) :: !ors;
               else
                  let wctt1 = (match Hashtbl.find_option !wctt_opt y with | Some (t) -> t | None -> "1") in
                  str := ("(>= CD"^(string_of_int y)^"_"^x.node.name^" (+ CD"^(string_of_int y)^"_"^k^" "^wctt1^")) ")
              )
             )
             else str := "");
            !str
          ) x.node.incoming)) f) in
    doc ^ "))\n"
  ) lba); 

  adecl := List.unique !adecl;
  ors := List.unique !ors;
  ss := (
    (match List.is_empty !adecl with 
    | false -> (List.reduce (^) (List.map (fun x -> ("(declare-fun "^x^" () Int)\n")) (!adecl)))
    | true -> "")
    ^ !ss ^ 
      (match List.is_empty !ors with
      | false -> List.reduce (^) !ors
      | true -> "")
  );
  !ss

let print_constraint lba =
  let ss = List.reduce (^) 
    (List.mapi (fun r q ->
      if(((List.length lba) - 1) <> r) then
        List.reduce (^) (List.map (fun x ->
          List.reduce (^) (List.map (fun y ->
            let wctt1 = (match Hashtbl.find_option !wctt_opt r with | Some (t) -> t | None -> "1") in
            let wctt2 = (match Hashtbl.find_option !wctt_opt (r+1) with | Some (t) -> t | None -> "1") in
            ("(assert (or (>= CD"^(string_of_int r)^"_"^x.node.name^" (+ CD"^(string_of_int (r+1))^"_"^y.node.name^" "^wctt2^")) "^
                "(>= CD"^(string_of_int (r+1))^"_"^y.node.name^" (+ CD"^(string_of_int r)^"_"^x.node.name^" "^wctt1^"))))\n")
          ) (List.nth lba (r+1)))
        ) q)
      else
        ""
     )lba) 
  in
  ss       

let rec get_chan_prop logic node cc =
  match logic with
  | Or (t,l) -> get_chan_prop t node cc; get_chan_prop l node cc
  | Not (Proposition (Expr (t),p)) as s ->
    (match p with
    | [Some (Systemj.ChanPause ((Systemj.Ack|Systemj.Req), _,_))] ->
      cc := (node,s) :: !cc;
    | [None] -> ()
    | _ -> ())
  | Not (t) -> get_chan_prop t node cc
  | And (t,l) -> get_chan_prop  t node cc; get_chan_prop l node cc
  | Brackets (t) -> get_chan_prop  t node cc
  | NextTime (t) -> get_chan_prop  t node cc
  | Proposition (Expr (t),p) as s ->
    (match p with
    | [Some (Systemj.ChanPause ((Systemj.Ack|Systemj.Req), _,_))] ->
      cc := (node,s) :: !cc;
    | [None] -> ()
    | _ -> ())
  | True | False -> ()
  | Proposition _ -> ()

let remove_loop n = 
  if List.exists (fun x -> 
    (match x with
    | Proposition (_, [Some (ChanPause (Ack,Start,c))]) ->
      List.exists (fun x ->
        (match x with
        | (_, ChanPause (Req,Start,cc)) when 
            (match String.split c "_" with |(j,k) -> j) = (match String.split cc "_" with |(j,k) -> j) -> true
        | _ -> false
        )
      ) n.node.incoming_chan
    | Proposition (_, [Some (ChanPause (Ack,End,c))]) ->
      List.exists (fun x ->
        (match x with
        | (_, ChanPause (Req,End,cc)) when 
            (match String.split c "_" with |(j,k) -> j) = (match String.split cc "_" with |(j,k) -> j) -> true
        | _ -> false
        )
      ) n.node.incoming_chan
    | Proposition (_, [Some (ChanPause (Req,End,c))]) ->
      List.exists (fun x ->
        (match x with
        | (_, ChanPause (Ack,Start,cc)) when 
            (match String.split c "_" with |(j,k) -> j) = (match String.split cc "_" with |(j,k) -> j) -> true
        | _ -> false
        )
      ) n.node.incoming_chan
    | Proposition (_, [Some (ChanPause (Req,Start,c))]) -> true
    | _ -> false)
  ) n.tls then
(*     let tt = List.filter (fun x -> x <> n.node.name) n.node.incoming in *)
    let a = ref [] in
    let b = ref [] in
    (try
      List.iter2 (fun x y ->  if x <> n.node.name then( a := x :: !a; b := y :: !b ) ) n.node.incoming n.guards
    with
    | _ as s -> raise s);
    n.node.incoming <- !a;
    n.guards <- !b
  else
    ()

let getnames = function
  | (s,ss) ->
    match ss with 
    | Proposition (Expr (t),[Some (Systemj.ChanPause _ as p )]) ->
      ((match String.split t "_" with | (j,k) -> j), s, p)
    | Not (Proposition (Expr (t),[Some(Systemj.ChanPause _ as p )])) ->
      ((match String.split t "_" with | (j,k) -> j), s, p)
    | _ as t -> raise(Internal_error ("Unexpected channel proposition : "^(SS.to_string_hum (sexp_of_logic t))))

let insert_incoming i1 cdn1 i2 cdn2 =
  let first = getnames i1 in
  let second = getnames i2 in
  match first with 
  | (a,s,((Systemj.ChanPause (Systemj.Ack, Systemj.Start,_)) as pp) (*"ack",true*) ) -> 
    (match second with 
    | (aa,ss,((Systemj.ChanPause (Systemj.Req, Systemj.Start,_)) as p) (*"req",false*) ) when a = aa ->
      s.node.incoming_chan <- (("CD"^(string_of_int cdn2)^"_"^ss.node.name),p) :: s.node.incoming_chan;
    | (aa,ss,Systemj.ChanPause (Systemj.Req, Systemj.End,_) (*"req",true*) ) when a = aa ->
      ss.node.incoming_chan <- (("CD"^(string_of_int cdn1)^"_"^s.node.name),pp) :: ss.node.incoming_chan;
    | _ -> ())
  | (a,s,Systemj.ChanPause (Systemj.Ack, Systemj.End,_) (*"ack",false*) ) ->
    (match second with 
    | (aa,ss,((Systemj.ChanPause (Systemj.Req, Systemj.End,_)) as p) (*"req",true*) ) when a = aa ->
      s.node.incoming_chan <- (("CD"^(string_of_int cdn2)^"_"^ss.node.name),p) :: s.node.incoming_chan;
    | _ -> ())
  | (a,s,((Systemj.ChanPause (Systemj.Req, Systemj.End,_)) as pp) (*"req",true*) ) ->
    (match second with
    | (aa,ss,((Systemj.ChanPause (Systemj.Ack, Systemj.Start,_) as p)) (*"ack",true*) ) when a = aa ->
      s.node.incoming_chan <- (("CD"^(string_of_int cdn2)^"_"^ss.node.name),p) :: s.node.incoming_chan;
    | (aa,ss,Systemj.ChanPause (Systemj.Ack, Systemj.End,_) (*"ack",false*) ) when a = aa ->
      ss.node.incoming_chan <- (("CD"^(string_of_int cdn1)^"_"^s.node.name), pp) :: ss.node.incoming_chan;
    | _ -> ())
  | (a,s,((Systemj.ChanPause (Systemj.Req, Systemj.Start,_)) as pp) (*"req",false*) ) ->
    (match second with
    | (aa,ss,Systemj.ChanPause (Systemj.Ack, Systemj.Start,_) (*"ack",true*) ) when a = aa ->
      ss.node.incoming_chan <- (("CD"^(string_of_int cdn1)^"_"^s.node.name), pp ):: ss.node.incoming_chan;
    | _ -> ())
(* | _ -> () *)


let parse_option o =
  if o <> "" then
    (try
       let ic = open_in o in
       while true do
         let line = input_line ic in
         let lrval = String.split (String.trim line) "=" in
         let rval = (match lrval with | (l,r) -> String.trim r) in
         let lval = String.nsplit (match lrval with | (l,r) -> String.trim l) "." in
         (match lval with
         | ["CD";num;"WCTT"] ->
           (* let cdnum = (int_of_string num) in *)
           Hashtbl.replace !wctt_opt (int_of_string num) rval
         | ["CD";num;"WCRT"] ->
           (* let cdnum = (int_of_string num) in *)
           Hashtbl.replace !wcrt_opt (int_of_string num) rval
         | _ as t -> raise (Internal_error ("Wrong smt option format : "^
					       (SSL.string_of_sexp (SSL.sexp_of_list SSL.sexp_of_string t))))
         );()
       done
     with
     | End_of_file -> ()
     | Sys_error e -> raise (Internal_error e)
     | _ as t -> prerr_endline "Wrong smt option format"; raise t
    );
  ()

let get_last_node lb =
  let incoming_list = List.concat (List.map (fun x -> x.node.incoming) lb) in
  List.filter (fun x -> List.for_all (fun y -> x.node.name <> y ) incoming_list ) lb

let print_wcrt lba =
  let wcrt = List.fold_left (^) ("") (List.mapi (fun i x -> 
    let node = get_last_node x in
    List.fold_left (^) ("") (List.map (fun l ->
      (match (Hashtbl.find_option !wcrt_opt i,Hashtbl.find_option !wctt_opt i) with
      | (Some (x),Some(z)) -> ("(assert (and (<= (+ CD"^(string_of_int i)^"_"^(l.node.name)^" "^z^") "^x^")))\n")
      | _ -> ("; CD "^(string_of_int i)^" : none\n")
      )
    ) node)
  ) lba) in
  let wcrt = ("; -- WCRT constraints -- \n"^wcrt) in
  wcrt

let get_update_sigs index g =
  let updates = Util.get_updates index g in
  print_endline "DEEEEEBUG   ";
  let () =   SS.output_hum Pervasives.stdout (SSL.sexp_of_list sexp_of_proposition updates) in
  let updates = List.sort_unique compare ((List.map 
    (fun x -> (match x with | Update x ->x | _ ->  raise (Internal_error "Cannot happen!!"))))
    (List.filter (fun x -> (match x with | Update _ ->true | _ -> false)) updates)) in
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
          if x.[0] = '$' then 
            true
          else(
            let ii = List.exists (fun y -> x = y ) isignals in
            let up = List.exists (fun y -> x = y ) updates in
            print_endline (node.node.name^"-- yes -- to "^outnode);
            List.iter (fun x -> print_endline ("updates "^x)) updates;
            List.iter (fun x -> print_endline ("internal_signals "^x)) internal_signals;
            print_endline x;
            print_endline ("ii||up : "^(string_of_bool (ii||up)));
            ii || up
          );
      | _ -> true (* Ignoring data atm *)
      )
  | Not (Proposition (x,_)) as s->
      (match x with 
      | Expr x -> 
          if x.[0] = '$' then 
            let () = SS.output_hum Pervasives.stdout (sexp_of_logic s) in
            raise (Internal_error "^^^^^^^^^^^^ Not emit proposition impossible!")
          else(
            let ii = List.exists (fun y -> x = y ) isignals in
            let up = List.for_all (fun y -> x <> y ) updates in
            print_endline (node.node.name^"-- no -- to "^outnode);
            List.iter (fun x -> print_endline ("updates "^x)) updates;
            List.iter (fun x -> print_endline ("internal_signals "^x)) internal_signals;
            print_endline ("NOT "^x);
            print_endline ("ii||up : "^(string_of_bool (ii||up)));
            ii || up
          )
      | _ -> true (* Ignoring data atm *)
      )
  | True -> true
  | False -> false
  | _ as s -> 
    let () = SS.output_hum Pervasives.stdout (sexp_of_logic s) in
    raise (Internal_error ("Got a non known proposition type in smt" ))

(*
  let to_false = ref signals in
  let () = List.iter (fun x -> to_false := List.filter (fun y -> y <> x) !to_false) updates in
  let () = List.iter (fun x -> to_false := List.filter (fun y -> y <> x) !to_false) isignals in
  let g = Util.label "smt" !to_false internal_signals channels index updates isignals asignals (match outgoing with | (a,b) -> b) in
  let a = (function (b,c) -> b) outgoing in
  print_endline (node.node.name^" to "^a^" evaluated to "^g);
  let () = List.iter (fun x -> print_endline ("tofalse "^x)) !to_false in
*)

let remove_unreachable index lb channels internal_signals signals isignals asignals =
  let o = Hashtbl.create 1000 in
  let () = List.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) lb in
  let unreachables_all = 
    List.flatten (List.map (fun node ->    
      print_endline ("ANALYZING "^node.node.name);
      let updates = List.map (fun x -> get_update_sigs index x) node.guards in
      print_endline "update all --==== ";
      let () = List.iter (fun x -> 
          SS.output_hum Pervasives.stdout (SSL.sexp_of_list SSL.sexp_of_string x)) updates  in
      print_endline "\nupdate ends ----";
(*       List.iter (fun x -> List.iter (fun x -> print_endline ("AAAA "^x)) x) updates; *)
      let olists = match Hashtbl.find_option o node.node.name with | Some (l) -> l | _ -> [] in
      let unreachables = List.map (fun outgoing -> 
        print_endline "outgoins :";
        let () = SS.output_hum Pervasives.stdout (sexp_of_logic ((fun (a,b) -> b) outgoing) ) in
        print_endline ("\nupdate size :"^(string_of_int (List.length updates)));

        let result = 
          (match node.tlabels with
          | Proposition (Label "st",_) ->
              false
          | _ ->
            List.for_all2 (fun update incoming -> 
              if (incoming <> node.node.name) then(
                print_endline "\nupdate";
                let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list SSL.sexp_of_string update)  in
                print_endline "";
                not(eval node update channels internal_signals signals isignals asignals index 
                    ((fun (a,b) -> a ) outgoing) ((fun (a,b) -> b) outgoing) ) 
              )
              else(
                print_endline "returning here true";
                true
              )
            ) updates node.node.incoming (* assuming order of updates, incoming and guards are the same *)
          ) in

        print_endline ("outgoins done "^(string_of_bool result));

        if result then
           (fun (a,b) -> Some (a,node.node.name)) outgoing (* (node, incoming) node need to rem incoming and its corrs guards *)
        else
          None
       ) olists in
      List.iter (function
        | Some (x,y) -> 
            print_endline ("unreachables : from "^y^ " to "^x) 
        | None -> ()
       ) unreachables;
      print_endline "=======================";
      unreachables
  ) lb )
  in 

  let unreachables_all = List.filter (fun x -> x <> None) unreachables_all in
  (* First removing edges (incomings) *)
  let () = List.iter (fun n -> 
    List.iter (function Some (remn,remin) ->
      if(n.node.name = remn) then(
        let ig = List.map2 (fun incoming guard -> if remin <> incoming then Some (incoming,guard) else None ) n.node.incoming n.guards in
        let ig = List.filter (function | Some _ -> true | None -> false ) ig in
        let ig = List.map (function | Some ((_) as a) -> a ) ig in
        let ig = List.split ig in
        let () = (fun (i,g) -> n.node.incoming <- i; n.guards <- g) ig in
        ()
      )
    ) unreachables_all
  ) lb in
  (* Second traverse the graph and remove unreachable nodes *)
(*
  let o = Hashtbl.create 1000 in
  let () = List.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) lb in
*)
  let newlb = ref [] in
  let st = List.filter (fun x -> match x.tlabels with | Proposition (Label "st",_) -> true | _ -> false ) lb in
  newlb := (List.hd st) :: !newlb;
  let r = ref true in
  while !r do
    r := List.fold_left (||) false (List.map (fun node ->
      if List.for_all (fun x -> x.node.name <> node.node.name ) !newlb then
          if List.exists (fun x -> List.exists (fun y-> x = y.node.name ) !newlb  ) node.node.incoming then(
            newlb := node :: !newlb;
            print_int (List.length !newlb);
            print_endline "";
            true
          )
          else
            false
      else
        false
        ) lb) 
  done

let make_smt lba filename channels internal_signals signals isignals asignals =
  let cc = ref [] in
  let () = List.iter (fun x -> 
    let o = Hashtbl.create 1000 in
    let () = List.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) x in
    let cc2 = ref [] in 
    List.iter (fun y ->  
      List.iter (fun k -> get_chan_prop k y cc2 ) 
	(List.map (fun x -> 
	  (match x with
          | (name,logic) when name <> y.node.name ->
            logic
          | _ -> True)
	 ) (match Hashtbl.find_option o y.node.name with Some x -> x | None -> [("",True)])) ) x; 
    cc := !cc2 :: !cc) lba in
  
  cc := List.rev !cc;

  let () = List.iteri (fun i x ->
    if (((List.length !cc) - 1) <> i) then
      List.iter (fun i1 ->
        List.iter (fun i2 ->
          insert_incoming i1 i i2 (i+1)
	) (List.nth !cc (i+1)) 
      ) x
  ) !cc in

  let () = List.iter (fun x -> List.iter (fun x -> remove_loop x) x) lba in
  let lbatmp = Util.map7 remove_unreachable (List.init (List.length lba) (fun x -> x)) lba channels internal_signals signals isignals asignals in

  let fd = open_out filename in   
  let decl_stuff = 
    ("(set-option :produce-proofs true)\n" >> text) ++
      ("(set-logic QF_IDL)\n" >> text) ++
      ((print_states lba) >> text) ++
      ((print_sequentiality lba) >> text) ++
      ((print_constraint lba) >> text) ++
      ((print_wcrt lba) >> text)++
      ("(check-sat)\n(get-model)\n(get-proof)\n" >> text)
  in
  let () = print ~output:(output_string fd) decl_stuff in
  close_out fd



