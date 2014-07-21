module List = Batteries.List
module Hashtbl = Batteries.Hashtbl
module MyString = Batteries.String

module SS = Sexplib.Sexp
module SSL = Sexplib.Std

module PL = PropositionalLogic
open TableauBuchiAutomataGeneration

let (|>) x f = f x

type configuration = {
  mutable formula : string;
  mutable smtopt: string;
  mutable oPromela: string;
  mutable oJava: string;
  mutable oSmt2: string;
  mutable oC: string;
  mutable dot: bool ref
}

let usage_msg = "Usage: systemjc [OPTIONS] <filename>\nsee -help for more options" in
let conf = {
  formula="";smtopt="";oPromela="";oJava="";
  oSmt2="";oC="";dot=ref false
} in
let file_name = ref "" in
let speclist = Arg.align [
    ("-promela", Arg.String (fun x ->  conf.oPromela <- x),
     "<file>     The name of the promela output file");
    ("-smt2", Arg.String (fun x -> conf.oSmt2 <- x), 
     "<file>     The name of the SMT-LIB output file");
    ("-C", Arg.String (fun x -> conf.oC <- x), 
     "<file>     Generate C backend");
    ("-java", Arg.String (fun x -> conf.oJava <- x), 
     "<package>  Generate Java backend");
    ("-sopt", Arg.String (fun x -> conf.smtopt <- x), 
     "<file>     The name of the optional file for SMT-LIB output generation");
    ("-formula", Arg.String (fun x -> conf.formula <- x), 
     "<file>     The propositional linear temporal logic formula to verify\n\
     \                      (see promela ltl man page)");
    ("-dot", Arg.Set conf.dot, 
     "           Generate dot files for the Buchi automatas")
  ] in

try
  let () = Arg.parse speclist (fun x -> file_name := x) usage_msg in
  (* Initialize the error reporting structures *)
  let mytime = Sys.time() in
  let in_chan = open_in !file_name in
  let () = print_endline "....Lexing and parsing..." in
  let lexbuf = Lexing.from_channel in_chan in
  let ast = Parser.ast Lexer.lexer lexbuf in
  (* Close the input channel *)
  let () = close_in in_chan in 
  let () = print_endline "....Rewriting the ast ..." in
  let () = IFDEF DEBUG THEN SS.output_hum Pervasives.stdout (Systemj.sexp_of_ast ast); print_endline "" ELSE () ENDIF in
  let () = flush_all () in
  let channels = List.sort_unique compare (List.flatten (List.map Systemj.collect_channels 
                                                           (match ast with |Systemj.Apar(x,_)->x))) in
  let () = IFDEF DEBUG THEN SS.output_hum Pervasives.stdout (Systemj.sexp_of_ast ast); print_endline "" ELSE () ENDIF in
  let () = flush_all () in
  let ast = PropositionalLogic.rewrite_ast ast in
  let () = print_endline "....Building Propositional logic trees ..." in
  let ltls = PropositionalLogic.build_propositional_tree_logic ast in
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
      let () = SS.output_hum Pervasives.stdout (PropositionalLogic.sexp_of_logic x) in
      print_endline "\n\n\n\n\n\n-----------------------------------------------\n\n\n\n") ltls ELSE () ENDIF in
  let () = print_endline "....Building Buchi Automata ..." in
  let () = if conf.!dot then
      Dot.generate_ltls ltls ((Filename.chop_extension !file_name)^"_ltls")
  in

  (* let buchi_automatas = List.mapi TableauBuchiAutomataGeneration.create_graph ltls in *)
  let buchi_automatas = Parmap.parmapi ~ncores:4 TableauBuchiAutomataGeneration.create_graph (Parmap.L ltls) in
  (* let ccount = List.init (List.length ltls) (fun x -> x) in *)
  (* let ltls1 = List.combine ccount ltls in *)
  (* let () = Functory.Cores.set_number_of_cores 4 in *)
  (* let buchi_automatas = Functory.Cores.map (fun (x,y) -> TableauBuchiAutomataGeneration.create_graph x y) ltls1 in *)
  let labeled_buchi_automatas = List.map2 TableauBuchiAutomataGeneration.add_labels ltls buchi_automatas in
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
      let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
      print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
  let () = if conf.!dot then
      Dot.generate_dot labeled_buchi_automatas ((Filename.chop_extension !file_name)^"_lgba_01_") 
  in

  let () = List.iter ModelSystem.propagate_guards_from_st labeled_buchi_automatas in
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
      let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
      print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
  let () = if conf.!dot then
      Dot.generate_dot labeled_buchi_automatas ((Filename.chop_extension !file_name)^"_lgba_02_") 
  in

  let init = ref [] in
  let labeled_buchi_automatas = 
    List.mapi (fun i x -> 
        let () = List.iter ModelSystem.make x in
        let () = List.iter ModelSystem.replace (List.of_enum (Hashtbl.values ModelSystem.tbl)) in 
        let () = Hashtbl.clear ModelSystem.replaced in 
        (* let () = Hashtbl.clear ModelSystem.guards in  *)
        let ret = List.of_enum (Hashtbl.values ModelSystem.tbl) in
        let () = Hashtbl.clear ModelSystem.tbl in
        let ret = List.filter (fun {node=n} -> n.old <> []) ret in
        let () = flush_all () in
        let st_node = List.find (fun {tlabels=t} -> (match t with | PL.Proposition (PL.Label x,_) -> x = "st" | _ -> false)) ret in
        init := st_node.node.name :: !init;
        let () = print_endline "....Building SystemJ model......" in
        let () = IFDEF DEBUG THEN List.iter (fun x -> 
            let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
            print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
        let () = List.iter (fun ({node=n} as ln) -> 
            let gg = ref [] in
            let ig = ref [] in
            for c = 0 to (List.length ln.guards)-1 do
              if (List.nth n.incoming c) <> "Init" then
                gg := !gg @ [(List.nth ln.guards c)]
              else
                ig := !ig @ [(List.nth ln.guards c)]
            done;
            if !ig <> [] then
              (* This is the only way this should be allowed: 1.) If there
                 	     are multiple Init's then that means you could have run this
                 	     thing with an || 2.) But, if there is a parent node, then
                 	     that node needs to have been true for this node to have
                 	     been executed. -- At least, that's the theory!
                 	  *)
              let ig = List.reduce (fun x y -> PL.Or(x,y)) !ig in
              gg := List.map (fun x -> PL.solve_logic (PL.And (x,ig))) !gg;
              ln.guards <- !gg;
              (* This is deleting the rest of the nodes with incoming as Init *)
              (* n.incoming <- List.remove_all n.incoming "Init"; *)
          ) ret in

        (* There are other nodes without "st", these can be logic
           	 formulas, in that case we need to find the nodes, which these
           	 nodes are a subformula of!  Note: 1.) I only look at Init nodes
           	 in this case.  2.) Replace the nodes with the new set of
           	 incoming nodes 3.) FIXME (IMP): If no replacements are possible
           	 then these nodes and their corresponding guards should be
           	 delted!  *)
        let torep = (List.filter(fun {tlabels=t} -> (match t with | PL.Proposition (PL.Label x,_) -> x <> "st" | _ -> true))
            (List.filter (fun{node=n} -> n.incoming=["Init"])ret)) in
        let () = List.iter(fun {node=n} -> n.incoming <- List.remove_all n.incoming "Init";) ret in
        let () = if conf.!dot then
            Dot.generate_dot ~th:(Some i) [ret] ((Filename.chop_extension !file_name)^"_lgba_03_") 
        in

        let (_,ret) = List.partition (fun {node=n} -> n.incoming = [] && n.name <> st_node.node.name) ret in
        let () = List.iter (ModelSystem.find_subformula_equivalents ret) torep in
        ret) labeled_buchi_automatas in
  (* This map is for each clock-domain *)
  let () = IFDEF DEBUG THEN List.iter (fun x -> 
      let () = print_endline "....Building SystemJ model......" in
      let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
      print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas ELSE () ENDIF in
  let () = if conf.!dot then
      Dot.generate_dot labeled_buchi_automatas ((Filename.chop_extension !file_name)^"_lgba_04_") 
  in

  (* Remove the unreachable nodes from the generated graph *)
  let labeled_buchi_automatas = List.map (Util.reachability []) labeled_buchi_automatas in
  let () = if conf.!dot then
      Dot.generate_dot labeled_buchi_automatas ((Filename.chop_extension !file_name)^"_lgba_05_") 
  in

  (* Removing unreachable edges and corresponding nodes before generating any backend codes - HJ *)
  let labeled_buchi_automatas = (
    let asignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_all_signal_declarations x) in
    let asignals = List.map (fun x -> List.sort_unique compare x) asignals in
    let signals = List.map (fun x -> List.split x) asignals |> List.split |> (fun (x,_) -> x) in
    let isignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_input_signal_declarations x) in
    let internal_signals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_internal_signal_declarations x) in
    let channel_strings = List.sort_unique compare (List.flatten (List.map (fun (x,_) -> x) channels)) in
    let labeled_buchi_automatas = Util.map7 
        Util.remove_unreachable (List.init (List.length labeled_buchi_automatas) (fun x -> x)) labeled_buchi_automatas 
        (List.init (List.length labeled_buchi_automatas) (fun x -> channel_strings)) internal_signals signals isignals asignals in
    labeled_buchi_automatas
  ) in
  let () = if conf.!dot then
      Dot.generate_dot labeled_buchi_automatas ((Filename.chop_extension !file_name)^"_lgba_06_") 
  in

  let () = 
    let () = 
      if conf.oPromela <> "" then
        try
          let asignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_all_signal_declarations x) in
          let asignals = List.map (fun x -> List.sort_unique compare x) asignals in
          let signals = List.map (fun x -> List.split x) asignals |> List.split |> (fun (x,_) -> x) in
          let signals_options = List.map (fun x -> List.split x) asignals |> List.split |> (fun (_,y) -> y) in
          let isignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_input_signal_declarations x) in
          let internal_signals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_internal_signal_declarations x) in
          let channel_strings = List.sort_unique compare (List.flatten (List.map (fun (x,_) -> x) channels)) in
          let var_decs = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.get_var_declarations x) |> List.flatten in
          let prom_make = Util.map8 
              Promela.make_promela 
              (List.init (List.length labeled_buchi_automatas) (fun x -> channel_strings)) internal_signals signals isignals
              (List.init (List.length labeled_buchi_automatas) (fun x -> x)) (List.rev !init) asignals labeled_buchi_automatas in
          let (promela_model,labeled_buchi_automatas) = List.split prom_make in
          let fd = open_out conf.oPromela in
          let promela_vardecs = List.fold_left Pretty.append Pretty.empty
              (List.map (fun x -> 
                   let (ttype,name) = (match x with | Systemj.SimTypedSymbol (t,Systemj.Symbol(y,_),_) -> t,y) in
                   ("c_code {" ^ (Systemj.get_data_type ttype) ^ " " ^ name ^ ";}\n" ^ 
                    "c_track \"&" ^ name ^ "\" " ^ "\"sizeof(" ^(Systemj.get_data_type ttype)^")\"\n") |> Pretty.text) var_decs) in
          let promela_channels = List.fold_left Pretty.append Pretty.empty 
              (List.map (fun x -> Pretty.text ("bool "^x^";\n"))channel_strings) in
          let promela_gsigs = List.fold_left Pretty.append Pretty.empty
              (Util.map2i (fun i y z -> 
                   List.fold_left Pretty.append Pretty.empty 
                     (List.map2 (fun x y -> 
                          Pretty.append (Pretty.text ("bool CD"^(string_of_int i)^"_"^x^";\n"))
                            (match y with
                             | None -> Pretty.empty
                             | Some r -> Pretty.append (Systemj.get_data_type_promela r.Systemj.data ^ " CD"^(string_of_int i)^"_"^x^"_val = "^r.Systemj.v^";\n"  |> Pretty.text)
                                           (Systemj.get_data_type_promela r.Systemj.data ^ " CD"^(string_of_int i)^"_"^x^"_val_pre;\n"  |> Pretty.text)
                            ))y z))signals signals_options) in
          let appf = if conf.formula = "" then Pretty.empty else (Pretty.text ("ltl {" ^ conf.formula ^ "}\n")) in
          let () = Pretty.print ~output:(output_string fd) 
              (Pretty.append promela_vardecs
                 (Pretty.append promela_gsigs
                    (Pretty.append promela_channels 
                       (Pretty.append appf
                          (List.reduce Pretty.append promela_model))))) in
          close_out fd;
        with
        | Sys_error _ as s -> raise s in
    let () = 
      if conf.oC <> "" then
        let fd = open_out conf.oC in
        let asignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_all_signal_declarations x) in
        let asignals = List.map (fun x -> List.sort_unique compare x) asignals in
        let signals = List.map (fun x -> List.split x) asignals |> List.split |> (fun (x,_) -> x) in
        let isignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_input_signal_declarations x) in
        let internal_signals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_internal_signal_declarations x) in
        let channel_strings = List.sort_unique compare (List.flatten (List.map (fun (x,_) -> x) channels)) in
        let c_model = Util.map8 
            C.make_c
            (List.init (List.length labeled_buchi_automatas) (fun x -> channel_strings)) internal_signals signals isignals
            (List.init (List.length labeled_buchi_automatas) (fun x -> x)) (List.rev !init) asignals labeled_buchi_automatas in
        let c_headers = Pretty.text ("#include <stdio.h>\n"^"typedef int bool;\n"^"#define true 1\n"^"#define false 0\n") in
        let var_decs = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.get_var_declarations x) |> List.flatten in
        let promela_vardecs = List.fold_left Pretty.append Pretty.empty
            (List.map (fun x -> 
                 let (ttype,name) = (match x with | Systemj.SimTypedSymbol (t,Systemj.Symbol(y,_),_) -> t,y) in
                 ((Systemj.get_data_type ttype) ^ " " ^ name ^ ";\n") |> Pretty.text) var_decs) in
        let c_main = C.make_main (List.length labeled_buchi_automatas) in
        let c_channels = List.fold_left Pretty.append Pretty.empty (List.map (fun x -> Pretty.text ("bool "^x^" = false;\n"))channel_strings) in
        let asignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_all_signal_declarations x) in
        let signals_options = List.map (fun x -> List.split x) asignals |> List.split |> (fun (_,y) -> y) in
        let signals = List.map (fun x -> List.split x) asignals |> List.split |> (fun (x,_) -> x) in
        let c_gsigs = List.fold_left Pretty.append Pretty.empty
            (Util.map2i (fun i y z -> 
                 List.fold_left Pretty.append Pretty.empty 
                   (List.map2 (fun x y -> 
                        Pretty.append (Pretty.text ("bool CD"^(string_of_int i)^"_"^x^";\n"))
                          (match y with
                           | None -> Pretty.empty
                           | Some r -> Pretty.append (Systemj.get_data_type_promela r.Systemj.data ^ " CD"^(string_of_int i)^"_"^x^"_val = "^r.Systemj.v^";\n"  
                                                      |> Pretty.text)
                                         (Systemj.get_data_type_promela r.Systemj.data ^ " CD"^(string_of_int i)^"_"^x^"_val_pre;\n"  |> Pretty.text)
                          ))y z))signals signals_options) in
        let c_labels = List.fold_left (Pretty.append) Pretty.empty (List.mapi (fun i x -> ("void *CD"^(string_of_int i)^"_L;\n") |> Pretty.text) labeled_buchi_automatas) in
        let () = Pretty.print ~output:(output_string fd) 
            (Pretty.append c_headers
               (Pretty.append promela_vardecs
                  (Pretty.append c_gsigs
                     (Pretty.append c_labels
                        (Pretty.append c_channels 
                           (Pretty.append(List.reduce Pretty.append c_model)
                              c_main)))))) in
        close_out fd in
    let () = 
      if conf.oJava <> "" then
        let asignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_all_signal_declarations x) in
        let asignals = List.map (fun x -> List.sort_unique compare x) asignals in
        let signals = List.map (fun x -> List.split x) asignals |> List.split |> (fun (x,_) -> x) in
        let isignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_input_signal_declarations x) in
        let internal_signals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_internal_signal_declarations x) in
        let channel_strings = List.sort_unique compare (List.flatten (List.map (fun (x,_) -> x) channels)) in
        let var_decs = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.get_var_declarations x) in
        let java_vardecs = (List.map (fun x -> List.fold_left Pretty.append Pretty.empty (List.map (fun x ->
            let (ttype,name) = (match x with | Systemj.SimTypedSymbol (t,Systemj.Symbol(y,_),_) -> t,y) in
            ("public "^(Systemj.get_data_type_promela ttype) ^ " " ^ name ^ ";\n") |> Pretty.text) x)) var_decs) in
        let java_channels = List.fold_left Pretty.append Pretty.empty 
            (List.map (fun x -> Pretty.text ("public static boolean "^x^" = false;\n"))channel_strings) in
        (*         let asignals = (match ast with | Systemj.Apar (x,_) -> List.map Systemj.collect_all_signal_declarations x) in *)
        let signals_options = List.map (fun x -> List.split x) asignals |> List.split |> (fun (_,y) -> y) in
        let java_interface_signals = List.fold_left Pretty.append Pretty.empty
            (Util.map2i (fun i y z -> 
                 List.fold_left Pretty.append Pretty.empty 
                   (List.map2 (fun x y -> 
                        if (not (List.exists (fun k -> k = x ) (List.nth internal_signals i))) then
                          Pretty.append (Pretty.text ("public static boolean CD"^(string_of_int i)^"_"^x^";\n"))
                            (match y with
                             | None -> Pretty.empty
                             | Some r -> Pretty.append ("public static "^Systemj.get_data_type_promela r.Systemj.data ^ " CD"^(string_of_int i)^"_"^x^"_val = "^r.Systemj.v^";\n"  
                                                        |> Pretty.text)
                                           ("public static "^Systemj.get_data_type_promela r.Systemj.data ^ " CD"^(string_of_int i)^"_"^x^"_val_pre;\n"  |> Pretty.text)
                            )
                        else Pretty.empty
                      )y z
                   )
               )signals signals_options) in
        let java_internal_signals_decl = 
          (Util.map2i (fun i y z -> 
               List.fold_left Pretty.append Pretty.empty 
                 (List.map2 (fun x y -> 
                      if (List.exists (fun k -> k = x ) (List.nth internal_signals i)) then
                        Pretty.append (Pretty.text ("public static boolean CD"^(string_of_int i)^"_"^x^";\n"))
                          (match y with
                           | None -> Pretty.empty
                           | Some r -> Pretty.append ("public static "^Systemj.get_data_type_promela r.Systemj.data ^ " CD"^(string_of_int i)^"_"^x^"_val = "^r.Systemj.v^";\n"  
                                                      |> Pretty.text)
                                         ("public static "^Systemj.get_data_type_promela r.Systemj.data ^ " CD"^(string_of_int i)^"_"^x^"_val_pre;\n"  |> Pretty.text)
                          )
                      else Pretty.empty
                    )y z
                 )
             )signals signals_options) in

        let java_model = Util.map8
            Java.make_java
            (List.init (List.length labeled_buchi_automatas) (fun x -> channel_strings)) internal_signals signals isignals
            (List.init (List.length labeled_buchi_automatas) (fun x -> x)) (List.rev !init) asignals labeled_buchi_automatas in

        let fnwe = conf.oJava in
        let () = if(Sys.file_exists fnwe) then 
            Util.remove_dir fnwe
        in
        let () = Unix.mkdir fnwe 0o770 in

        let java_main = Java.make_main (List.length labeled_buchi_automatas) (Filename.basename fnwe)  in
        let fd_com = open_out (fnwe^"/Interface.java") in
        let fd_main = open_out (fnwe^"/Main.java") in
        let fd_cdintf = open_out (fnwe^"/ClockDomain.java") in
        let () = Pretty.print ~output:(output_string fd_com) (Java.make_interface java_channels java_interface_signals (Filename.basename fnwe)) in
        let () = Pretty.print ~output:(output_string fd_main) java_main in
        let () = Pretty.print ~output:(output_string fd_cdintf) (Java.make_cdintf (Filename.basename fnwe)) in
        let () = Java.make_scj_wrapper (Filename.basename fnwe) (Filename.dirname fnwe) (List.length labeled_buchi_automatas) in

        let jclass = List.mapi (fun i x -> 
            (("package "^(Filename.basename fnwe)^
              ";\npublic class CD"^(string_of_int i)^" implements ClockDomain {\n") |> Pretty.text) ) labeled_buchi_automatas in
        let jclass = List.map2 (fun x y -> Pretty.append x y) jclass java_internal_signals_decl in
        let jclass = List.map2 (fun x y -> Pretty.append x y) jclass java_vardecs in
        let jclass = List.map2 (fun x y -> Pretty.append x y) jclass java_model in
        let jclass = List.map (fun x -> Pretty.append x ("}\n" |> Pretty.text)) jclass  in

        let () = List.iteri (fun i x -> 
            let fd = open_out (fnwe^"/CD"^(string_of_int i)^".java") in
            let () = Pretty.print ~output:(output_string fd) x in
            close_out fd
          ) jclass in
        let () = close_out fd_com in
        close_out fd_com;
        close_out fd_cdintf;
        close_out fd_main
    in
    let () = 
      if conf.oSmt2 <> "" then
        let () = Smt.parse_option conf.smtopt in
        let () = Smt.make_smt labeled_buchi_automatas conf.oSmt2 in 
        () 
    in
(*
    let () = List.iter (fun x -> 
      let () = SS.output_hum Pervasives.stdout (SSL.sexp_of_list TableauBuchiAutomataGeneration.sexp_of_labeled_graph_node x) in
      print_endline "\n\n\n\n\n\n-----------------------------------------------------\n\n\n\n") labeled_buchi_automatas in
*)
    let () = Printf.printf "Execution time: %fs\n" (Sys.time() -. mytime) in
    () in ()
with
| End_of_file -> exit 0
| Sys_error  _ -> Arg.usage speclist usage_msg
| _ as s -> raise s
