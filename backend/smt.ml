module List = Batteries.List
module SS = Sexplib.Sexp
module SSL = Sexplib.Std
open Pretty
open TableauBuchiAutomataGeneration
open PropositionalLogic
let (++) = append
let (>>) x f = f x

exception Internal_error of string

let print_states lba =
  let ss = List.reduce (^) (List.mapi (fun y f ->  
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

let make_smt lba filename =
  let fd = open_out filename in   
  let decl_stuff = ("(set-logic QF_IDL)\n" >> text) ++
    ((print_states lba) >> text) ++
    ((print_sequentiality lba) >> text) ++
    ((print_constraint lba) >> text) ++
    ("(check-sat)\n(get-model)\n" >> text)
  in
  let () = print ~output:(output_string fd) decl_stuff in
  close_out fd



