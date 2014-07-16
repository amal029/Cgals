
open TableauBuchiAutomataGeneration
open Pretty
module PL = PropositionalLogic
module L = Batteries.List

let (|>) x f = f x
let (++) = Pretty.append

let genEachCD lgbaCD =
  ("digraph G{\n" |> text)
  ++ ("www" |> text)
(*   L.iter (fun x -> print_endline x.node.name ) lgbaCD *)
  

let generate_dot lgba filename =
  let dotdoc = Pretty.empty in
  let gvs = L.map (fun x -> genEachCD x ) lgba in
  let () = L.iteri (fun i x -> 
    let fd = open_out (filename^"CD"^(string_of_int i)^".gv") in
    let () = Pretty.print ~output:(output_string fd) x in
    close_out fd
  ) gvs in

  ()
