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
    (List.reduce (^) (List.map (fun k -> "(declare-fun CD"^(string_of_int y)^"_"^k.node.name^" () Int)\n") f) )) lba) in
  ss 

let print_sequentiality lba =
  let ss = List.reduce (^) (List.mapi (fun y f ->
    let doc = List.fold_left (^) ("(assert (and " ) 
      (List.map (fun x -> 
        if (x.tlabels = Proposition (Label "st")) then
          ("(>= CD"^(string_of_int y)^"_"^x.node.name^" 0) ")
        else
          List.reduce (^) (List.map (fun k -> 
	    if List.exists (fun tt -> tt.node.name = k) f then
              ("(>= CD"^(string_of_int y)^"_"^x.node.name^" (+ CD"^(string_of_int y)^"_"^k^" 1)) ")
	    else ""
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
    | Not (Proposition (Expr (t))) as s->
            if((String.ends_with t "_req") || (String.ends_with t "_ack")) then
                cc := (node,s) :: !cc
(*                 ;print_endline ("Here is Not expr "^t) *)
    | Not (t) -> get_chan_prop t node cc
    | And (t,l) -> get_chan_prop t node cc; get_chan_prop  l node cc
    | Brackets (t) -> get_chan_prop t node cc
    | NextTime (t) -> get_chan_prop t node cc
    | Proposition (Expr (t)) as s ->
            if((String.ends_with t "_req") || (String.ends_with t "_ack")) then
                cc := (node,s) :: !cc
(*                 ;print_endline ("Here is Expr ::: "^t) *)
    | Proposition (Label (t) | Update (t)) -> ()
    | _ as t -> raise (Internal_error "Error during channel analysis")


let get_refs i1 chan dir isnot =
    match i1 with
    | (s,ss) ->
        match ss with 
        | Proposition (Expr (t)) ->
                chan := (match String.split t "_" with | (j,k) -> j);
                dir := (match String.split t "_" with | (j,k) -> k);
                isnot := false
        | Not (Proposition (Expr (t))) ->
                chan := (match String.split t "_" with | (j,k) -> j) ;
                dir := (match String.split t "_" with | (j,k) -> k) ;
                isnot := true

let insert_incoming i1 i2 =
    let chan1 = ref "" in
    let dir1 = ref "" in
    let isnot1 = ref false in
    let chan2 = ref "" in
    let dir2 = ref "" in
    let isnot2 = ref false in
    let () = get_refs i1 chan1 dir1 isnot1 in
    let () = get_refs i2 chan2 dir2 isnot2 in
(*     Finish this tomorr *)
    ()

let make_smt lba filename =
  let cc = ref [] in
  let () = List.iter (fun x -> let cc2 = ref [] in List.iter (fun y ->  
                      List.iter (fun k -> get_chan_prop k y cc2 ) y.node.next) x ; cc := !cc2 :: !cc) lba in

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

  let () = List.iteri (fun i x ->
      if (((List.length !cc) - 1) <> i) then
          List.iter (fun i1 ->
              List.iter (fun i2 ->
                  print_endline "entered ";
                  insert_incoming i1 i2
      ) (List.nth !cc (i+1)) 
      ) (List.nth !cc i)
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



