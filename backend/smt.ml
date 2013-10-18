module List = Batteries.List 
module SS = Sexplib.Sexp 
module SSL = Sexplib.Std 
module String = Batteries.String 
open Pretty 
open TableauBuchiAutomataGeneration 
open PropositionalLogic 
let (++) = append 
let (>>) x f = f x

exception Internal_error of string

let print_states lba = let ss = List.reduce (^) (List.mapi (fun y f ->  
  (List.reduce (^) (List.map (fun k -> "(declare-fun CD"^(string_of_int y)^"_"^k.node.name^" () Int)\n") f) )) lba) in ss 

let print_sequentiality lba =
  let adecl = ref [] in
  let ors_string = ref "" in
  let ors = ref [] in
  let ss = ref "" in
  ss := List.reduce (^) (List.mapi (fun y f ->
    let ors2 = ref [] in
    let doc = List.fold_left (^) ("(assert (and " ) 
      (List.map (fun x -> 
        if (x.tlabels = Proposition (Label "st",[None])) then
          ("(>= CD"^(string_of_int y)^"_"^x.node.name^" 0) ")
        else
          List.reduce (^) (List.map (fun k -> 
            let str = ref "" in
            (if List.exists (fun tt -> tt.node.name = k) f then
                str := ("(>= CD"^(string_of_int y)^"_"^x.node.name^" (+ CD"^(string_of_int y)^"_"^k^" 1)) ")
             else str := "");

            (* Insering micro states *)
            x.node.incoming_chan <- (List.unique x.node.incoming_chan);
            (if (List.is_empty x.node.incoming_chan = false)  then
                let () = List.iter (fun z -> 
                    (match z with
                    | Proposition (Label (s),_) ->
                        let microst = ("CD"^(string_of_int y)^"_"^x.node.name^"-"^s) in
(*                         let tutu = ("(declare-fun "^microst^" () Int)") in *)
                        adecl := microst :: !adecl;
                        List.iter(fun u ->
                            (match (String.split s "@", (match u with | (inchan,Systemj.ChanPause (g,h,l)) -> (inchan,g,h,l) )) with
                            | (("$AckStart",cn), (inchan,Systemj.Req,Systemj.Start,l)) 
                            | (("$AckEnd",cn), (inchan,Systemj.Req,Systemj.End,l))
                            | (("$ReqEnd",cn), (inchan,Systemj.Ack,Systemj.Start,l)) 
                            when (match String.split cn "_" with | (x,_) -> x) = (match String.split l "_" with | (x,_) -> x) -> 
                                    print_endline (cn^"    - >    "^l);
                                    str := (!str^" (>= "^microst^" (+ "^inchan^" 1)) ");
                                    ors2 := ("(>= CD"^(string_of_int y)^"_"^x.node.name^" "^microst^") ") :: !ors2;
                            | _ -> ()
                            );
                            str := (!str^" (>= "^microst^" (+ CD"^(string_of_int y)^"_"^k^" 1)) ")
                        ) x.node.incoming_chan

                    | _ -> () )
                    ) x.tls in
                    ()
             );

(*
            (if (List.is_empty x.node.incoming_chan = false)  then
                List.iteri (fun i l -> 
                    match l with
                    | (s,_) ->
                    str := (!str ^"(>= CD"^(string_of_int y)^"_"^x.node.name^" (+ "^s^" 1)) ") ) x.node.incoming_chan
            );
*)
            !str
          ) x.node.incoming)) f) in
    ors := !ors2 :: !ors;
    doc ^ "))\n"
  ) lba); 

  if ((List.is_empty !ors) = false) then
      ors_string := List.reduce (^) (List.map (fun x -> ((List.fold_left (^) ("(assert (or ") x) ^"))\n") ) !ors);
  ss := (
      (List.reduce (^) (List.map (fun x -> ("(declare-fun "^x^" () Int)\n")) (List.unique !adecl)))
      ^ !ss ^ !ors_string);
  !ss

let print_constraint lba =
  let ss = List.reduce (^) 
    (List.mapi (fun r q ->
      if(((List.length lba) - 1) <> r) then
        List.reduce (^) (List.map (fun x ->
          List.reduce (^) (List.map (fun y ->
            ("(assert (or (>= CD"^(string_of_int r)^"_"^x.node.name^" (+ CD"^(string_of_int (r+1))^"_"^y.node.name^" 1)) "^
                "(>= CD"^(string_of_int (r+1))^"_"^y.node.name^" (+ CD"^(string_of_int r)^"_"^x.node.name^" 1))))\n")
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
  | Not (Proposition (Expr (t),p)) as s->
          (match p with
          | [Some (Systemj.ChanPause ((Systemj.Ack|Systemj.Req), _,_))] ->
            cc := (node,s) :: !cc;
          | [None] -> ()
          | [_] as t -> print_endline ""; print_int (List.length t); print_endline ""; raise(Internal_error "Unexpected channel list")
          | _ -> ())
(*     let () = print_endline ("Inserting "^node.node.name^" Not "^t) in *)
(*
        print_endline ("--- NODE "^node.node.name^" ----");
        let () = SS.output_hum Pervasives.stdout (PropositionalLogic.sexp_of_logic s) in
        print_endline "-----------";
*)
  | Not (t) -> get_chan_prop t node cc
  | And (t,l) -> get_chan_prop  t node cc; get_chan_prop l node cc
  | Brackets (t) -> get_chan_prop  t node cc
  | NextTime (t) -> get_chan_prop  t node cc
  | Proposition (Expr (t),p) as s ->
          (match p with
          | [Some (Systemj.ChanPause ((Systemj.Ack|Systemj.Req), _,_))] ->
            cc := (node,s) :: !cc;
          | [None] -> ()
          | [_] as t -> print_endline ""; print_int (List.length t); print_endline ""; raise(Internal_error "Unexpected channel list")
          | _ -> ())
  | Proposition ((Label _ | Update _), _) -> ()
  | True | False -> ()
  | _ as t -> raise (Internal_error ((SS.to_string_hum (sexp_of_logic t)) ^ "Error during channel analysis"))


let getnames = function
  | (s,ss) ->
    let tt = List.filter (fun x -> x <> s.node.name) s.node.incoming in
    s.node.incoming <- tt;
    match ss with 
    | Proposition (Expr (t),[Some (Systemj.ChanPause _ as p )]) ->
      ((match String.split t "_" with | (j,k) -> j), s, p)
    | Not (Proposition (Expr (t),[Some(Systemj.ChanPause _ as p )])) ->
      ((match String.split t "_" with | (j,k) -> j), s, p)
    | _ as t -> raise(Internal_error ("Unexpected channel proposition : "^(SS.to_string_hum (sexp_of_logic t))))

let insert_incoming i1 cdn1 i2 cdn2 =
  let first = getnames i1 in
  let second = getnames i2 in
  (* (match first with | (a,b,c,d) -> print_endline (a^" "^b.node.name^" "^c^" "^(string_of_bool d))); *)
  (* (match second with | (a,b,c,d) -> print_endline (a^" "^b.node.name^" "^c^" "^(string_of_bool d))); *)
  (* print_endline "----"; *)
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
  | _ -> ()

let make_smt lba filename =
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
  (*
    print_int (List.length !cc);
    print_endline "";
    let () = List.iteri (fun y x -> 
    print_endline ("CD "^(string_of_int y)^"-------");
    List.iter(fun y ->
    let () = SS.output_hum Pervasives.stdout (PropositionalLogic.sexp_of_logic (
    match y with
    | (_,ss) -> ss
    )) in
    print_endline "";
    ()
    ) x
    ) !cc in
  *)
  (* let () = List.iter (fun y -> List.iter(fun (x,_) -> SS.output_hum stdout (sexp_of_labeled_graph_node x)) y) !cc in *)
  let () = List.iteri (fun i x ->
    if (((List.length !cc) - 1) <> i) then
      List.iter (fun i1 ->
        List.iter (fun i2 ->
          insert_incoming i1 i i2 (i+1)
	) (List.nth !cc (i+1)) 
      ) x
  ) !cc in

  let fd = open_out filename in   
  let decl_stuff = ("(set-logic QF_IDL)\n" >> text) ++
    ((print_states lba) >> text) ++
    ((print_sequentiality lba) >> text) ++
    ((print_constraint lba) >> text) ++
    ("(check-sat)\n(get-model)\n" >> text)
  in
  let () = print ~output:(output_string fd) decl_stuff in
  close_out fd



