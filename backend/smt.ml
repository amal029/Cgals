module List = Batteries.List 
module SS = Sexplib.Sexp 
module SSL = Sexplib.Std 
module String = Batteries.String 
module Hashtbl = Batteries.Hashtbl
module Enum = Batteries.Enum
module Random = Batteries.Random
open Systemj
open Pretty 
open TableauBuchiAutomataGeneration 
open PropositionalLogic 
let (++) = append 
let (>>) x f = f x
(* let wctt_opt = ref (Hashtbl.create 10) *)
(* let wcrt_opt = ref (Hashtbl.create 10) *)
let grouplist = ref [] 

exception Internal_error of string

let print_states lba = let ss = List.reduce (^) (List.mapi (fun y f ->  
    (List.reduce (^) (List.map (fun k -> "(declare-fun CD"^(string_of_int
                                                              y)^"_"^k.node.name^" () Real)\n") f) )) lba) in ss 

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
                 List.reduce (^) (List.map2 (fun k iWCRT -> 
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
(*                                        let wctt1 = (match Hashtbl.find_option !wctt_opt y with | Some (t) -> t | None -> "1") in *)
                                       str := (!str^" (>= "^microst^" (+ CD"^(string_of_int y)^"_"^k^" "^iWCRT^")) ");
                                       (match (p, (match u with | (inchan,Systemj.ChanPause (g,h,l)) -> (inchan,g,h,l) )) with
                                         | (ChanPause (Ack,Start,cn) (*("$AckStart",cn)*), (inchan,Systemj.Req,Systemj.Start,l)) 
                                         | (ChanPause (Ack,End,cn) (*("$AckEnd",cn)*), (inchan,Systemj.Req,Systemj.End,l))
                                         | (ChanPause (Req,End,cn) (*("$ReqEnd",cn)*), (inchan,Systemj.Ack,Systemj.Start,l)) 
                                           when (match String.split cn "_" with | (x,_) -> x) = (match String.split l "_" with | (x,_) -> x) -> 
                                           (* macrostate can finish when any of one of deps finish for the same microst  *)
                                           let cd_nodename = (String.nsplit inchan "_") in
                                           let cdnum = int_of_string (String.lchop ~n:2 (List.at cd_nodename 0)) in
                                           let node_list = List.at lba cdnum in 
                                           let node_from_other_cd = List.find (fun x -> x.node.name = (List.at cd_nodename 1) ) node_list in
                                           let oWCRT = match node_from_other_cd.node.oWCRT with | Some l -> l | None -> "0" in
(*                                            let wctt1 = (match Hashtbl.find_option !wctt_opt cdnum with | Some (t) -> t | None -> "1") in *)
                                           multdep := (" (>= "^microst^" (+ "^inchan^" "^oWCRT^")) ") :: !multdep;
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
(*                             let wctt1 = (match Hashtbl.find_option !wctt_opt y with | Some (t) -> t | None -> "1") in *)
                            str := ("(>= CD"^(string_of_int y)^"_"^x.node.name^" (+ CD"^(string_of_int y)^"_"^k^" "^iWCRT^")) ")
                         )
                       )
                      else str := "");
                     !str
                   ) x.node.incoming x.node.iWCRT)) f) in
      doc ^ "))\n"
    ) lba); 

  adecl := List.unique !adecl;
  ors := List.unique !ors;
  ss := (
    (match List.is_empty !adecl with 
     | false -> (List.reduce (^) (List.map (fun x -> ("(declare-fun "^x^" () Real)\n")) (!adecl)))
     | true -> "")
    ^ !ss ^ 
    (match List.is_empty !ors with
     | false -> List.reduce (^) !ors
     | true -> "")
  );
  !ss

let print_constraint lba group =
  let ss = 
    (List.mapi (fun r q ->
         List.mapi (fun rr tt -> 
             if( r < rr ) then(
               List.reduce (^) (List.map (fun x ->
                   List.reduce (^) (List.map (fun y ->
(*                        let wctt1 = (match Hashtbl.find_option !wctt_opt r with | Some (t) -> t | None -> "1") in *)
(*                        let wctt2 = (match Hashtbl.find_option !wctt_opt (r+1) with | Some (t) -> t | None -> "1") in *)
                       let xnum = string_of_int r in
                       let ynum = string_of_int rr in
                       match Hashtbl.find_option group xnum with
                       | None ->
                         ""
                       | Some g ->
                         if( List.exists (fun y -> y = ynum) g ) then
                           let oWCRT2 = match y.node.oWCRT with | Some l ->l | None -> "0" in 
                           let oWCRT1 = match x.node.oWCRT with | Some l ->l | None -> "0" in 
                           ("(assert (or (>= CD"^(string_of_int r)^"_"^x.node.name^" (+ CD"^(string_of_int rr)^"_"^y.node.name^" "^oWCRT2^")) "^
                            "(>= CD"^(string_of_int rr)^"_"^y.node.name^" (+ CD"^(string_of_int r)^"_"^x.node.name^" "^oWCRT1^"))))\n")
                         else
                           ""
                     ) tt)
                 ) q)
             )
             else
               ""
           ) lba;
       )lba) >> List.flatten >> List.reduce (^) 
  in
  ss       

let rec get_chan_prop logic node cc =
  match logic with
  | Not (Proposition (Label (t),p)) as s -> ()
  | Proposition (Label (t),p) as s ->
    (match p with
     | [Some (Systemj.ChanPause ((Systemj.Ack|Systemj.Req), _,_))] ->
       cc := (node,s) :: !cc;
     | [None] -> ()
     | _ -> ())
  | _ -> ()

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
    | Proposition (Label _,[Some (Systemj.ChanPause (a,b,c) as p )]) ->
      ((match String.split c "_" with | (j,k) -> j), s, p)
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
         let lval = (match lrval with | (l,r) -> String.trim l) in
         let index = 0 in
         (* Distributing clock-domains *)
         (if (lval = "group") then
            let group = Hashtbl.create 10 in
            let dlist = Str.split (Str.regexp "|") rval in
            let dlist = List.map (fun x -> Str.split (Str.regexp ",") x ) dlist in
            let () = List.iter (fun x -> 
                List.iter(fun y ->
                    match Hashtbl.find_option group y with
                    | Some _ ->
                      raise (Internal_error ("Duplicated CD number in group"))
                    | None ->
                      Hashtbl.add group y x
                  ) x
              ) dlist in
            grouplist := !grouplist @ [group] )
(*
         else
           let lval = String.nsplit lval "." in
           (match lval with
            | ["CD";num;"WCTT"] ->
              (* let cdnum = (int_of_string num) in *)
              Hashtbl.replace !wctt_opt (int_of_string num) rval
            | ["CD";num;"WCRT"] ->
              (* let cdnum = (int_of_string num) in *)
              Hashtbl.replace !wcrt_opt (int_of_string num) rval
            | _ as t -> raise (Internal_error ("Wrong smt option format : "^
                                               (SSL.string_of_sexp (SSL.sexp_of_list SSL.sexp_of_string t))))
           );
*)
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

(*
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
*)

let insert_iWCRT lba =
  let () = Random.init (int_of_float (Unix.gettimeofday ())) in
  let () = List.iter (fun node_set -> 
      List.iter (fun node ->
          List.iter (fun incoming -> 
             node.node.iWCRT <- (string_of_int ((Random.int 9)+1)) :: node.node.iWCRT
            ) node.node.incoming
        ) node_set
    ) lba in

(*   Debugging *)
(*
  let () = List.iteri (fun i x -> 
      print_endline ("CD "^(string_of_int i));
      List.iter (fun x ->
          print_endline ("Node : "^x.node.name);
          print_endline ("incoming : ");
          List.iter2 (fun y z -> print_endline (y^" wcrt :"^z)) x.node.incoming x.node.iWCRT
        ) x
    )lba in
*)

(*   Now calc WCRT of outgoing edges *)
  let oWCRTs = Hashtbl.create 1000 in
  let () = List.iter (fun cd_nodes -> 
      let () = Hashtbl.clear oWCRTs in
      let () = List.iter (fun node -> 
          List.iter2 (fun incoming iwcrt ->
              match Hashtbl.find_option oWCRTs incoming with
              | Some l -> 
                if ((int_of_string iwcrt) > (int_of_string l)) then
                  Hashtbl.replace oWCRTs incoming iwcrt
              | None -> Hashtbl.add oWCRTs incoming iwcrt
            ) node.node.incoming node.node.iWCRT
        ) cd_nodes in
(*       We now have owcrt of nodes, but incoming is a string so find the node from lba and insert owcrt *)
      Hashtbl.iter (fun k v -> 
(*         There are some nodes in the set 'incoming' but NOT in lba!!! WTF! *)
          try
            let node = List.find (fun node -> k = node.node.name ) cd_nodes in
            node.node.oWCRT <- Some v
          with | Not_found -> ()
        ) oWCRTs
    ) lba in

(*   Debugging *)
(*
  List.iter (fun x ->  
      List.iter (fun x -> 
          print_endline ("Node "^x.node.name^" WCRT : "^((function Some x -> x | None -> "0" ) x.node.oWCRT));
        ) x
    ) lba;
*)

  ()


let make_smt lba filename =
  let cc = ref [] in
  let () = List.iter (fun x -> 
(*     o is not used here so I am commenting this out *)
(*       let o = Hashtbl.create 1000 in *)
(*       let () = List.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) x in *)
      let cc2 = ref [] in 
      List.iter (fun y ->  
          List.iter (fun k -> get_chan_prop k y cc2 ) y.tls ) x;
      cc := !cc2 :: !cc) lba in

  cc := List.rev !cc;

  let () = List.iteri (fun i x ->
      List.iteri (fun y z ->
          if(i <> y) then(
            List.iter (fun i1 ->
                List.iter (fun i2 ->
                    insert_incoming i1 i i2 y
                  ) z
              ) x
          )
        ) !cc
    ) !cc in

  let () = List.iter (fun x -> List.iter (fun x -> remove_loop x) x) lba in

(*   Inserting WCRT for incoming edges *)
  let () = insert_iWCRT lba in

  let decl_stuff = 
    ("(set-option :produce-proofs true)\n" >> text) ++
    ("(set-logic QF_LRA)\n" >> text) ++
    ((print_states lba) >> text) ++
    ((print_sequentiality lba) >> text)
  in
  if ((List.is_empty !grouplist) = true) then
    let fd = open_out filename in   
    let decl_stuff = decl_stuff ++ 
                     ((print_constraint lba (Hashtbl.create 1)) >> text) ++
                     ("(check-sat)\n(get-model)\n(get-proof)\n" >> text) in
    let () = print ~output:(output_string fd) decl_stuff in
    close_out fd;
  else
    List.iteri (fun i group -> 
        let fd = open_out (filename^(string_of_int i)^".smt2") in   
        let decl_stuff = decl_stuff ++ 
                         ((print_constraint lba group) >> text) ++
                         ("(check-sat)\n(get-model)\n(get-proof)\n" >> text) 
        in
        let () = print ~output:(output_string fd) decl_stuff in
        close_out fd
      ) !grouplist



