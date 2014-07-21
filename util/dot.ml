open TableauBuchiAutomataGeneration
open Pretty

module PL = PropositionalLogic
module L = Batteries.List

let (|>) x f = f x
let (++) = Pretty.append

let rec get_prop = function
  | PL.Label x -> x
  | PL.Expr x -> x
  | PL.Update x -> x
  | PL.DataExpr x -> "DataExpr"
  | PL.DataUpdate x -> "DataUpdate"

let rec guards_to_string = function
  | PL.True -> "true"
  | PL.False -> "false"
  | PL.Or (x,y) -> (guards_to_string x)^"||"^(guards_to_string y)
  | PL.Not x -> "!"^(guards_to_string x)
  | PL.And (x,y) -> (guards_to_string x)^"&&"^(guards_to_string y)
  | PL.Proposition (p,_) -> (get_prop p)
  | PL.Brackets x -> "("^(guards_to_string x)^")"
  | PL.NextTime x -> "X"^(guards_to_string x)

let genEachCD lgbaCD =
  ("digraph G{\n" |> text)
  ++ ("// Generating node connection\n" |> text)
  ++ ((L.fold_left (fun conc n -> 
      conc^(L.fold_left2 (fun conc incoming guard -> 
          conc^incoming^" -> "^n.node.name^" [ label=\""^(guards_to_string guard)^"\" ]\n") "" n.node.incoming n.guards)
    ) "" lgbaCD ) |> text )
  ++ ("}" |> text)
(*   L.iter (fun x -> print_endline x.node.name ) lgbaCD *)

let generate_ltls ltls filename =
  L.iteri (fun i ltl ->
      let ltl_string = guards_to_string ltl in
      let fd = open_out (filename^"CD"^(string_of_int i)^".txt") in
      let () = Pretty.print ~output:(output_string fd) (ltl_string |> text) in
      close_out fd
    ) ltls
  

let generate_dot ?(th=None) lgba filename =
  match th with
  | None -> 
    let gvs = L.map (fun x -> genEachCD x ) lgba in
    L.iteri (fun i x -> 
        let fd = open_out (filename^"CD"^(string_of_int i)^".gv") in
        let () = Pretty.print ~output:(output_string fd) x in
        close_out fd
      ) gvs 
  | Some i -> 
    let x = genEachCD (L.first lgba) in
    let fd = open_out (filename^"CD"^(string_of_int i)^".gv") in
    let () = Pretty.print ~output:(output_string fd) x in
    close_out fd
