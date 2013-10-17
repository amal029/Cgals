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
  let ss = List.reduce (^) (List.mapi (fun y f ->
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
            (if (List.is_empty x.node.incoming_chan = false)  then
                List.iteri (fun i l -> 
                    str := (!str ^"(>= CD"^(string_of_int y)^"_"^x.node.name^" (+ "^l^" 1)) ") ) x.node.incoming_chan
            );
            !str
          ) x.node.incoming)) f) in

    doc ^ "))\n"
  ) lba) in
  ss

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
  | Not (Proposition (Expr (t),_)) as s->
    if((String.ends_with t "_req") || (String.ends_with t "_ack")) then
(*     let () = print_endline ("Inserting "^node.node.name^" Not "^t) in *)
        cc := (node,s) :: !cc;
        print_endline ("--- NODE "^node.node.name^" ----");
        let () = SS.output_hum Pervasives.stdout (PropositionalLogic.sexp_of_logic s) in
        print_endline "-----------";
  | Not (t) -> get_chan_prop t node cc
  | And (t,l) -> get_chan_prop  t node cc; get_chan_prop l node cc
  | Brackets (t) -> get_chan_prop  t node cc
  | NextTime (t) -> get_chan_prop  t node cc
  | Proposition (Expr (t),_) as s ->
    if((String.ends_with t "_req") || (String.ends_with t "_ack")) then
(*     let () = print_endline ("Inserting "^node.node.name^" "^t) in *)
        cc := (node,s) :: !cc;
        print_endline ("--- NODE "^node.node.name^" ----");
        let () = SS.output_hum Pervasives.stdout (PropositionalLogic.sexp_of_logic s) in
        print_endline "-----------";
  | Proposition ((Label _ | Update _), _) -> ()
  | True | False -> ()
  | _ as t -> raise (Internal_error ((SS.to_string_hum (sexp_of_logic t)) ^ "Error during channel analysis"))


let getnames = function
  | (s,ss) ->
    let tt = List.filter (fun x -> x <> s.node.name) s.node.incoming in
    s.node.incoming <- tt;
    match ss with 
    | Proposition (Expr (t),_) ->
      ((match String.split t "_" with | (j,k) -> j), s, (match String.split t "_" with | (j,k) -> k), true)
    | Not (Proposition (Expr (t),_)) ->
      ((match String.split t "_" with | (j,k) -> j), s, (match String.split t "_" with | (j,k) -> k), false)
    | _ -> raise(Internal_error "Error during channel analysis")

let insert_incoming i1 cdn1 i2 cdn2 =
  let first = getnames i1 in
  let second = getnames i2 in
  (* (match first with | (a,b,c,d) -> print_endline (a^" "^b.node.name^" "^c^" "^(string_of_bool d))); *)
  (* (match second with | (a,b,c,d) -> print_endline (a^" "^b.node.name^" "^c^" "^(string_of_bool d))); *)
  (* print_endline "----"; *)
  match first with 
  | (a,s,"ack",true) -> 
    (match second with 
    | (aa,ss,"req",false) when a = aa ->
      s.node.incoming_chan <- ("CD"^(string_of_int cdn2)^"_"^ss.node.name) :: s.node.incoming_chan;
    | (aa,ss,"req",true) when a = aa ->
      ss.node.incoming_chan <- ("CD"^(string_of_int cdn1)^"_"^s.node.name):: s.node.incoming_chan;
    | _ -> ())
  | (a,s,"ack",false) ->
    (match second with 
    | (aa,ss,"req",true) when a = aa ->
      s.node.incoming_chan <- ("CD"^(string_of_int cdn2)^"_"^ss.node.name):: s.node.incoming_chan;
    | _ -> ())
  | (a,s,"req",true) ->
    (match second with
    | (aa,ss,"ack",true) when a = aa ->
      s.node.incoming_chan <- ("CD"^(string_of_int cdn2)^"_"^ss.node.name):: s.node.incoming_chan;
    | (aa,ss,"ack",false) when a = aa ->
      ss.node.incoming_chan <- ("CD"^(string_of_int cdn1)^"_"^s.node.name):: s.node.incoming_chan;
    | _ -> ())
  | (a,s,"req",false) ->
    (match second with
    | (aa,ss,"ack",true) when a = aa ->
      ss.node.incoming_chan <- ("CD"^(string_of_int cdn1)^"_"^s.node.name):: s.node.incoming_chan;
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



