module String = Batteries.String
module L = Batteries.List
module Hashtbl = Batteries.Hashtbl
module LL = Batteries.LazyList

open Sexplib
open Std
open Sexp
open PropositionalLogic
open TableauBuchiAutomataGeneration

exception Internal_error of string

open Pretty

let (++) = append
let (>>) x f = f x
let (|>) x f = f x

let make_switch index = function
  | ({name=n},tlabel,_) -> 
    ("case "^(String.lchop n)^":\n" >> text)
    ++(("CD"^(string_of_int index)^"_"^n^ "();  /*" ^ (string_of_logic tlabel) ^ "*/" ^ "\n") >> text)
    ++ ("break;\n" >> text)

let getInterfaceString is s =
  if (L.exists (fun x -> x = s) is) then
    ""
  else
    ("Interface.")

let make_body asignals internal_signals channels o index signals isignals = function
  (* Make the body of the process!! *)
  | ({name=n},tlabel,_) -> 
    let o = (match Hashtbl.find_option o n with Some x -> x | None -> []) in
    let (o,guards) = L.split o in
    (* Now add the transitions *)
    ("case "^(String.lchop n)^":/*"^(string_of_logic tlabel)^"*/"^"\n" >> text)
    ++ (L.reduce (++) (
        if o <> [] then
          L.map2 (fun x g ->
              (* let updates = ref [] in *)
              let updates = Util.get_updates index g in
              (* let updates1 = List.sort_unique compare (List.map (fun (Update x) ->x) updates) in *)
              let datastmts = (L.filter (fun x -> (match x with | DataUpdate _ ->true | _ -> false)) updates) in
              let updates1 = List.sort_unique compare ((List.map 
                                                          (fun x -> (match x with | Update x ->x | _ ->  raise (Internal_error "Cannot happen!!"))))
                                                         (List.filter (fun x -> (match x with | Update _ ->true | _ -> false)) updates)) in
              let to_false = ref signals in
              let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) updates1 in
              let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) isignals in
              let g = Util.label "java" !to_false internal_signals channels index updates [] asignals g in
              let updates = updates1 in
              let asignals_names = List.split asignals |> (fun (x,_) -> x) in
              let asignals_options = List.split asignals |> (fun (_,y) -> y) in
              if g <> "false" then
                ("if" >> text)
                ++ ((if g <> "" then ("(" ^ g ^ ") {\n") else "") >> text)
                ++ ("resetCD();\n" >> text)
                (* These are the updates to be made here!! *)
                ++ L.fold_left (++) empty (L.mapi (fun i x -> 
                    ((if not (L.exists (fun t -> t = x) channels) then 
                        ((getInterfaceString internal_signals x)^"CD"^(string_of_int index)^"_"^x) else (getInterfaceString internal_signals x)^x)
                     ^ " = true;\nSystem.out.println(\"Emitted: "^x^"\");\n") >> text) updates)
                ++ ((L.fold_left (^) "" (L.map (Util.build_data_stmt asignals index "java" internal_signals) datastmts)) >> text)
                ++ (("state = " ^(String.lchop x)^ ";\n") >> text)
                ++ ("break;\n" >> text)
                ++ ("}\n" >> text)
              else empty
            ) o guards
        else [("state =  " ^(String.lchop n)^ "; break;\n">> text)]
      )) 

let make_interface java_channels java_gsigs fnwe =
  ("package "^fnwe^";\n" >> text)
  ++ ("public class Interface {\n" >> text)
  ++ java_gsigs
  ++ java_channels
  ++ ("}\n" >> text)

let make_cdintf fnwe =
  ("package "^fnwe^";\n" >> text)
  ++ ("public interface ClockDomain {\n" >> text)
  ++ ("public void run (); \n" >> text)
  ++("}\n" >> text)

let make_reset signals isignals asignals internal_signals channels index =
  let asignals_names = List.split asignals |> (fun (x,_) -> x) in
  let asignals_options = List.split asignals |> (fun (_,y) -> y) in
  let to_false = ref signals in
  let () = L.iter (fun x -> to_false := L.filter (fun y -> y <> x) !to_false) isignals in
  ("public void resetCD() {\n" >> text)
    ++ L.fold_left (++) empty (Util.map2i (fun i x y -> 
        (match y with
         | None -> Pretty.empty
         | Some r -> 
           ((getInterfaceString internal_signals x)^"CD"^(string_of_int index)^"_"^x^"_val_pre = "
            ^(getInterfaceString internal_signals x)^"CD" ^ (string_of_int index)^"_"^x^"_val;\n" >> Pretty.text)
           ++ ((getInterfaceString internal_signals x)^"CD"^(string_of_int index)^"_"^x^"_val = "^r.Systemj.v^";\n"  >> Pretty.text)
        ))asignals_names asignals_options)
    ++ L.fold_left (++) empty (L.mapi (fun i x ->
        ((if not (L.exists (fun t -> t = x) channels) then 
            ((getInterfaceString internal_signals x)^"CD"^(string_of_int index)^"_"^x) else (getInterfaceString internal_signals x)^x)
         ^ " = false;\n" >> text)) !to_false)
    ++ ("}\n" >> text)



let make_process internal_signals channels o index signals isignals init asignals lgn = 
  (("public int state = " ^(String.lchop init)^"; // This must be from immortal mem\n") >> text)
  ++ ((make_reset signals isignals asignals internal_signals channels index))
  ++ ("public void run(){\n" >> text)
  ++ ("switch (state){\n" >> text)
(*   ++ ((L.reduce (++) (L.map (fun x -> make_switch index (x.node,x.tlabels,x.guards)) lgn)) >> (4 >> indent)) *)
  ++ ((L.reduce (++) (L.map (fun x -> make_body asignals internal_signals channels o index signals isignals (x.node,x.tlabels,x.guards)) lgn)) >> (4 >> indent))
  ++ ("default: System.err.println(\"System went to a wrong state !! \"+state); break;\n" >> text)
  ++ ("}\n}\n" >> text)
  ++ (" " >> line)

let make_main index file_name = 
  let tt = 
    (("package "^file_name^";\n") >> text)
    ++ ("public class Main {\n" >> text)
    ++ ("public static void main(String args[]){\n" >> text)
    ++ (L.fold_left (++) empty (L.init index (fun x -> "CD"^(string_of_int x)^" cd"^(string_of_int x)^" = new CD"^(string_of_int x)^"();\n" >> text)))
    ++ ("while(true){\n" >> text) 
    ++ (L.fold_left (++) empty (L.init index (fun x -> "cd"^(string_of_int x)^".run();\n" >> text)))
    ++ ("}\n" >> text) 
    ++ ("}\n" >> text)
    ++ ("}\n" >> text) in
  let () = IFDEF DEBUG THEN print_endline "I am trying to make Java main" ELSE () ENDIF in
  let () = IFDEF DEBUG THEN (print tt) ELSE () ENDIF in tt


let make_java channels internal_signals signals isignals index init asignals lgn = 
  let o = Hashtbl.create 1000 in
  let () = L.iter (fun x -> Util.get_outgoings o (x.node,x.guards)) lgn in
  group ((make_process internal_signals channels o index signals isignals init asignals lgn) ++ (" " >> line))

let make_scj_wrapper basename dirname size =
  let headers = 
    ("package "^basename^".scj;\n" >> text) ++
    ("import javax.realtime.*;\n" >> text) ++
    ("import javax.safetycritical.*;\n\n" >> text) ++
    ("import "^basename^".*;\n\n" >> text) in
  let main = 
    ("public class Level0Mission extends CyclicExecutive implements Safelet<CyclicExecutive>{\n" >> text) ++
    ("private static final long PERIOD = 10;\n" >> text) ++
    ("private static final long DURATION = 10;\n" >> text) ++
    ("private static final long MISSION_MEMORY_SIZE = 1024;\n " >> text) ++
    ("private static final long IMMORTAL_MEMORY_SIZE = 1024;\n " >> text) ++
    ("\n// Mission implementations - goes to Mission memory\n" >> text) ++
    ("@Override\nprotected void initialize() {\n" >> text) ++
    ("int i = 0;\n" >> text) ++
    (
      L.fold_left (fun s x -> 
          s ++ 
          (("SchedulableGALSObject so"^x^" = new SchedulableGALSObject(\n") >> text)++
          ("new PriorityParameters(i++),\n" >> text) ++
          ("new PeriodicParameters(null, new RelativeTime(Level0Mission.PERIOD, 0)),\n" >> text) ++
          ("new StorageParameters(1024,null),\n">> text)++
          ("1024 /* INSERT_SCOPE_SIZE_HERE */);\n" >> text) ++
          (("CD"^x^ " cd"^x^" = new CD"^x^"();\n") >> text) ++
          (("so"^x^".setClockDomain(cd"^x^");\n") >> text) ++
          (("so"^x^".register();\n") >> text)
        ) empty (List.init size (fun x -> string_of_int x))
    ) ++ ("}\n" >> text) ++
    ("@Override\npublic long missionMemorySize() {\
      return Level0Mission.MISSION_MEMORY_SIZE;}\n" >> text) ++
    ("@Override\npublic CyclicSchedule getSchedule(PeriodicEventHandler[] handlers) {\n\
      Frame[] frames = new Frame[1];\n\
      frames[0] = new Frame(new RelativeTime(Level0Mission.DURATION, 0), handlers);\n\
      return new CyclicSchedule(frames);\n}\n\n" >> text) ++
    ("// Safelet implementations - goes to Immortal memory\n\
      @Override\npublic void initializeApplication() {}\n\
      @Override\npublic MissionSequencer<CyclicExecutive> getSequencer() {\n\
      StorageParameters sp = new StorageParameters(1024,null);\n\
      return new LinearMissionSequencer<CyclicExecutive>(new PriorityParameters(0),\n\
      sp,false,this);\n}\n" >> text) ++
    ("@Override\npublic long immortalMemorySize() {\n\
      return Level0Mission.IMMORTAL_MEMORY_SIZE;\n}\n" >> text) ++
    ("public static void main (String[] args) {\n\
      Safelet<CyclicExecutive> m = new Level0Mission();\n\
      JopSystem js = new JopSystem();\n\
      js.startCycle(m);\n\
      }\n}\n" >> text) in
  let galsobj =
    ("public class SchedulableGALSObject extends PeriodicEventHandler{  \n\
      	private ClockDomain cd;                                         \n\
      	public SchedulableGALSObject(PriorityParameters priority,       \n\
      			PeriodicParameters release, StorageParameters storage,      \n\
      			long scopeSize) {                                           \n\
      		super(priority, release, storage, scopeSize);                 \n\
      	}                                                               \n\
      	@Override                                                       \n\
      	public void handleAsyncEvent() { cd.run(); }                    \n\
      	public void setClockDomain(ClockDomain cdin){ this.cd = cdin; } \n\
      }" >> text) in
  let () = Unix.mkdir (dirname^"/"^basename^"/scj") 0o770 in
  let fd = open_out (dirname^"/"^basename^"/scj/Level0Mission.java") in
  let () = print ~output:(output_string fd) (headers ++ main) in
  let () = close_out fd in
  let fd = open_out (dirname^"/"^basename^"/scj/SchedulableGALSObject.java") in
  let () = print ~output:(output_string fd) (headers ++ galsobj) in
  let () = close_out fd in
  ()


