(**** PROFILING ****)
let ok_time = ref 0.0;;
let ko_time = ref 0.0;;

let profile f x =
 let before = Unix.gettimeofday () in
 let res = f x in
 let after = Unix.gettimeofday () in
 let delta = after -. before in
  if res then
   ok_time := !ok_time +. delta
  else
   ko_time := !ko_time +. delta;
  res
;;

let _ =
 Sys.catch_break true;
 at_exit
  (function () ->
    prerr_endline
     ("\nTIME SPENT IN CHECKING GOOD CONJECTURES: " ^ string_of_float !ok_time);
    prerr_endline
     ("TIME SPENT IN CHECKING BAD CONJECTURES: " ^ string_of_float !ko_time);)
;;

(**** END PROFILING ****)

type rel = Equal | SubsetEqual | SupersetEqual

let string_of_rel =
 function
    Equal -> "="
  | SubsetEqual -> "⊆"
  | SupersetEqual -> "⊇"

(* operator *)
type op = I | C | M

let string_of_op = function I -> "i" | C -> "c" | M -> "-"
let matita_of_op = function I -> "i" | C -> "c" | M -> "m"

(* compound operator *)
type compound_operator = op list

let string_of_cop op =
 if op = [] then "id" else String.concat "" (List.map string_of_op op)

let dot_of_cop op = "\"" ^ string_of_cop op ^ "\""

let matita_of_cop v =
 let rec aux =
  function
   | [] -> v
   | [op] -> matita_of_op op ^ " " ^ v
   | op::tl -> matita_of_op op ^ " (" ^ aux tl ^ ")"
 in
  aux

let name_of_theorem cop rel cop' =
 let cop,rel,cop' =
  match rel with
     Equal -> cop,"eq",cop'
   | SubsetEqual -> cop,"leq",cop'
   | SupersetEqual -> cop',"leq",cop
 in
  rel ^ "_" ^
   String.concat "" (List.map matita_of_op cop) ^ "_" ^
   String.concat "" (List.map matita_of_op cop')
;;

(* representative, other elements in the equivalence class,
   leq classes, geq classes *)
type equivalence_class =
 compound_operator * compound_operator list *
  equivalence_class list ref * equivalence_class list ref

let (===) (repr,_,_,_) (repr',_,_,_) = repr = repr';;
let (<=>) (repr,_,_,_) (repr',_,_,_) = repr <> repr';;

let string_of_equivalence_class (repr,others,leq,_) =
 String.concat " = " (List.map string_of_cop (repr::others)) ^
  (if !leq <> [] then
    "\n" ^
     String.concat "\n" 
      (List.map
        (function (repr',_,_,_) ->
           string_of_cop repr ^ " ⊆ " ^ string_of_cop repr') !leq)
   else
    "")

let dot_of_equivalence_class (repr,others,leq,_) =
 (if others <> [] then
   let eq = String.concat " = " (List.map string_of_cop (repr::others)) in
    dot_of_cop repr ^ "[label=\"" ^ eq ^ "\"];" ^
     if !leq = [] then "" else "\n"
  else if !leq = [] then
   dot_of_cop repr ^ ";"
  else
   "") ^
   String.concat "\n" 
    (List.map
      (function (repr',_,_,_) ->
         dot_of_cop repr' ^ " -> " ^ dot_of_cop repr ^ ";") !leq)

(* set of equivalence classes, infima, suprema *)
type set =
 equivalence_class list * equivalence_class list * equivalence_class list

let string_of_set (s,_,_) =
 String.concat "\n" (List.map string_of_equivalence_class s)

let ps_of_set (to_be_considered,under_consideration,news) ?processing (s,inf,sup) =
 let ch = open_out "xxx.dot" in
  output_string ch "digraph G {\n";
  (match under_consideration with
      None -> ()
    | Some repr ->
       output_string ch (dot_of_cop repr ^ " [color=yellow];"));
  List.iter
   (function (repr,_,_,_) ->
     if List.exists (function (repr',_,_,_) -> repr=repr') sup then
      output_string ch (dot_of_cop repr ^ " [shape=Mdiamond];")
     else
      output_string ch (dot_of_cop repr ^ " [shape=diamond];")
   ) inf ;
  List.iter
   (function (repr,_,_,_) ->
     if not (List.exists (function (repr',_,_,_) -> repr=repr') inf) then
      output_string ch (dot_of_cop repr ^ " [shape=polygon];")
   ) sup ;
  List.iter
   (function repr -> output_string ch (dot_of_cop repr ^ " [color=green];")
   ) to_be_considered ;
  List.iter
   (function repr -> output_string ch (dot_of_cop repr ^ " [color=navy];")
   ) news ;
  output_string ch (String.concat "\n" (List.map dot_of_equivalence_class s));
  output_string ch "\n";
  (match processing with
      None -> ()
    | Some (repr,rel,repr') ->
       output_string ch (dot_of_cop repr ^ " [color=red];");
       let repr,repr' =
        match rel with
           SupersetEqual -> repr',repr
         | Equal
         | SubsetEqual -> repr,repr'
       in
        output_string ch
         (dot_of_cop repr' ^ " -> " ^ dot_of_cop repr ^
          " [" ^
          (match rel with Equal -> "arrowhead=none " | _ -> "") ^
          "style=dashed];\n"));
  output_string ch "}\n";
  close_out ch;
  (*ignore (Unix.system "tred xxx.dot > yyy.dot && dot -Tps yyy.dot > xxx.ps")*)
  ignore (Unix.system "cp xxx.ps xxx_old.ps && dot -Tps xxx.dot > xxx.ps");
  (*ignore (read_line ())*)
;;

(******** communication with matitawiki ************)
let min_ch,mout_ch = Unix.open_process "../../../matitawiki.opt 2> /dev/null";;

let exec_cmd ?(undo=false) s =
 let un = if undo then "un" else "" in
(*prerr_endline ("<pgip><" ^ un ^ "doitem>" ^ s ^ "</" ^ un ^ "doitem></pgip>\n");*)
 output_string mout_ch ("<pgip><" ^ un ^ "doitem>" ^ s ^ "</" ^ un ^ "doitem></pgip>\n");
 flush mout_ch;
 let rec aux v =
  let l = input_line min_ch in
  let last = String.length l - 1 in
   assert (last > 0);
   if l.[last] = Char.chr 249 then
    int_of_string (String.sub l 0 last)
   else
    aux l
 in
  aux "x"
;;

let exec_cmds =
 let rec aux undopos =
  function
     [] -> true
   | he::tl ->
      let pos = exec_cmd he in
       if pos = -1 then
        begin
         match undopos with
            None -> assert false
          | Some undopos ->
             assert (exec_cmd ~undo:true (string_of_int (undopos - 1)) <> -1);
             false
        end
       else
        match undopos with
           None -> aux (Some pos) tl
         | _ -> aux undopos tl
 in
  aux None

let _ =
 assert (exec_cmd "set \"baseuri\" \"cic:/matita/theory_former\"." <> -1);
 assert (exec_cmd "include \"formal_topology.ma\"." <> -1);
;;

(********* testing a conjecture *******************)

let test to_be_considered_and_now ((s,_,_) as set) rel candidate repr =
 ps_of_set to_be_considered_and_now ~processing:(candidate,rel,repr) set;
 print_string
  (string_of_cop candidate ^ " " ^ string_of_rel rel ^ " " ^ string_of_cop repr ^ "? ");
 flush stdout;
(*
 assert (Unix.system "cat log.ma | sed s/^theorem/axiom/g | sed 's/\\. intros.*qed\\././g' > xxx.ma" = Unix.WEXITED 0);
 let ch = open_out_gen [Open_append] 0 "xxx.ma" in
*)
(*
 let i = ref 0 in
  List.iter
   (function (repr,others,leq,_) ->
     List.iter
      (function repr' ->
        incr i;
        output_string ch
         ("axiom ax" ^ string_of_int !i ^
          ": \\forall A." ^
           matita_of_cop "A" repr ^ " = " ^ matita_of_cop "A" repr' ^ ".\n");
      ) others;
     List.iter
      (function (repr',_,_,_) ->
        incr i;
        output_string ch
         ("axiom ax" ^ string_of_int !i ^
          ": \\forall A." ^
           matita_of_cop "A" repr ^ " ⊆ " ^ matita_of_cop "A" repr' ^ ".\n");
      ) !leq;
   ) s;
*)
  let candidate',rel',repr' =
   match rel with
      SupersetEqual -> repr,SubsetEqual,candidate
    | Equal
    | SubsetEqual -> candidate,rel,repr in
  let query1 =
   let name = name_of_theorem candidate' rel' repr' in
   ("theorem " ^ name ^ ": \\forall A." ^ matita_of_cop "A" candidate' ^
      " " ^ string_of_rel rel' ^ " " ^
      matita_of_cop "A" repr' ^ ".") in
  let query2 = "intros;" in
  let query3 = "autobatch size=8 depth=3 width=2." in
  let query4 = "qed." in
  let query = query1 ^ query2 ^ query3 ^ query4 in
(*
  output_string ch (query ^ "\n");
  close_out ch;
*)
  let res = profile exec_cmds [query1; query2; query3; query4] in
(*
  let res =
   (*Unix.system "../../../matitac.opt xxx.ma >> log 2>&1" = Unix.WEXITED 0*)
   profile Unix.system "../../../matitac.opt xxx.ma > /dev/null 2>&1" = Unix.WEXITED 0
  in
*)
   ignore (Unix.system "echo '(*' >> log.ma && cat xxx.dot >> log.ma && echo '*)' >> log.ma");
   let ch = open_out_gen [Open_append] 0o0600 "log.ma" in
   if res then
    output_string ch (query ^ "\n")
   else
    output_string ch ("(* " ^ query ^ "*)\n");
   close_out ch;
   print_endline (if res then "y" else "n");
   res

let remove node = List.filter (fun node' -> node <=> node');;

let add_leq_arc ((_,_,leq,_) as node) ((_,_,_,geq') as node') =
 leq := node' :: !leq;
 geq' := node :: !geq'
;;

let add_geq_arc ((_,_,_,geq) as node) ((_,_,leq',_) as node') =
 geq := node' :: !geq;
 leq' := node :: !leq'
;;

let remove_leq_arc ((_,_,leq,_) as node) ((_,_,_,geq') as node') =
 leq := remove node' !leq;
 geq' := remove node !geq'
;;

let remove_geq_arc ((_,_,_,geq) as node) ((_,_,leq',_) as node') =
 geq := remove node' !geq;
 leq' := remove node !leq'
;;

let leq_transitive_closure node node' =
 add_leq_arc node node';
 let rec remove_transitive_arcs ((_,_,_,geq) as node) (_,_,leq',_) =
  let rec remove_arcs_to_ascendents =
   function
      [] -> ()
    | (_,_,leq,_) as node'::tl ->
       remove_leq_arc node node';
       remove_arcs_to_ascendents (!leq@tl)
  in
   remove_arcs_to_ascendents !leq';
   List.iter (function son -> remove_transitive_arcs son node) !geq
 in
  remove_transitive_arcs node node'
;;

let geq_transitive_closure node node' =
 add_geq_arc node node';
 let rec remove_transitive_arcs ((_,_,leq,_) as node) (_,_,_,geq') =
  let rec remove_arcs_to_descendents =
   function
      [] -> ()
    | (_,_,_,geq) as node'::tl ->
       remove_geq_arc node node';
       remove_arcs_to_descendents (!geq@tl)
  in
   remove_arcs_to_descendents !geq';
   List.iter (function father -> remove_transitive_arcs father node) !leq
 in
  remove_transitive_arcs node node'
;;

let (@@) l1 n = if List.exists (function n' -> n===n') l1 then l1 else l1@[n]

let rec leq_reachable node =
 function
    [] -> false
  | node'::_ when node === node' -> true
  | (_,_,leq,_)::tl -> leq_reachable node (!leq@tl)
;;

let rec geq_reachable node =
 function
    [] -> false
  | node'::_ when node === node' -> true
  | (_,_,_,geq)::tl -> geq_reachable node (!geq@tl)
;;

exception SameEquivalenceClass of set * equivalence_class * equivalence_class;;

let locate_using_leq to_be_considered_and_now ((repr,_,leq,geq) as node)
 set start
=
 let rec aux ((nodes,inf,sup) as set) already_visited =
  function
     [] -> set
   | (repr',_,_,geq') as node' :: tl ->
       if List.exists (function n -> n===node') already_visited then
        aux set already_visited tl
       else if repr=repr' then aux set (node'::already_visited) (!geq'@tl)
       else if leq_reachable node' !leq then
        aux set (node'::already_visited) (!geq'@tl)
       else if (List.exists (function n -> not (geq_reachable n [node'])) !geq)
        then
         aux set (node'::already_visited) tl
       else if test to_be_considered_and_now set SubsetEqual repr repr' then
        begin
         if List.exists (function n -> n===node') !geq then
          (* We have found two equal nodes! *)
          raise (SameEquivalenceClass (set,node,node'))
         else
          begin
           let sup = remove node sup in
           let inf =
            if !geq' = [] then
             let inf = remove node' inf in
              if !geq = [] then
               inf@@node
              else
               inf
            else
             inf
            in
             leq_transitive_closure node node';
             aux (nodes,inf,sup) (node'::already_visited) (!geq'@tl)
          end
        end
       else
        aux set (node'::already_visited) tl
 in
  aux set [] start
;;

let locate_using_geq to_be_considered_and_now ((repr,_,leq,geq) as node)
 set start
=
 let rec aux ((nodes,inf,sup) as set) already_visited =
  function
     [] -> set
   | (repr',_,leq',_) as node' :: tl ->
       if List.exists (function n -> n===node') already_visited then
        aux set already_visited tl
       else if repr=repr' then aux set (node'::already_visited) (!leq'@tl)
       else if geq_reachable node' !geq then
        aux set (node'::already_visited) (!leq'@tl)
       else if (List.exists (function n -> not (leq_reachable n [node'])) !leq)
        then
         aux set (node'::already_visited) tl
       else if test to_be_considered_and_now set SupersetEqual repr repr' then
        begin
         if List.exists (function n -> n===node') !leq then
          (* We have found two equal nodes! *)
          raise (SameEquivalenceClass (set,node,node'))
         else
          begin
           let inf = remove node inf in
           let sup =
            if !leq' = [] then
             let sup = remove node' sup in
             if !leq = [] then
              sup@@node
             else
              sup
            else
             sup
           in
            geq_transitive_closure node node';
            aux (nodes,inf,sup) (node'::already_visited) (!leq'@tl)
          end
        end
       else
        aux set (node'::already_visited) tl
 in
  aux set [] start
;;

let analyze_one to_be_considered repr hecandidate (news,((nodes,inf,sup) as set)) =
if not (List.for_all (fun ((_,_,_,geq) as node) -> !geq = [] && let rec check_sups = function [] -> true | (_,_,leq,_) as node::tl -> if !leq = [] then List.exists (fun n -> n===node) sup && check_sups tl else check_sups (!leq@tl) in check_sups [node]) inf) then ((*ps_of_set ([],None,[]) set;*) assert false);
if not (List.for_all (fun ((_,_,leq,_) as node) -> !leq = [] && let rec check_infs = function [] -> true | (_,_,_,geq) as node::tl -> if !geq = [] then List.exists (fun n -> n===node) inf && check_infs tl else check_infs (!geq@tl) in check_infs [node]) sup) then (ps_of_set ([],None,[]) set; assert false);
 let candidate = hecandidate::repr in
  if List.length (List.filter ((=) M) candidate) > 1 then
   news,set
  else
   try
    let leq = ref [] in
    let geq = ref [] in
    let node = candidate,[],leq,geq in
    let nodes = nodes@[node] in
    let set = nodes,inf@[node],sup@[node] in
    let set,start_inf,start_sup =
     let repr_node =
      match List.filter (fun (repr',_,_,_) -> repr=repr') nodes with
         [node] -> node
       | _ -> assert false
     in
      match hecandidate,repr with
         I, I::_ -> raise (SameEquivalenceClass (set,node,repr_node))
       | I, _ ->
          add_leq_arc node repr_node;
          (nodes,remove repr_node inf@[node],sup),inf,sup
       | C, C::_ -> raise (SameEquivalenceClass (set,node,repr_node))
       | C, _ ->
          add_geq_arc node repr_node;
          (nodes,inf,remove repr_node sup@[node]),inf,sup
       | M, M::M::_ -> raise (SameEquivalenceClass (set,node,repr_node))
       | M, _ -> set,inf,sup
    in
    let set =
     locate_using_leq (to_be_considered,Some repr,news) node set start_sup in
(
let _,inf,sup = set in
if not (List.for_all (fun ((_,_,_,geq) as node) -> !geq = [] && let rec check_sups = function [] -> true | (_,_,leq,_) as node::tl -> if !leq = [] then List.exists (fun n -> n===node) sup && check_sups tl else check_sups (!leq@tl) in check_sups [node]) inf) then (ps_of_set ([],None,[]) set; assert false);
if not (List.for_all (fun ((_,_,leq,_) as node) -> !leq = [] && let rec check_infs = function [] -> true | (_,_,_,geq) as node::tl -> if !geq = [] then List.exists (fun n -> n===node) inf && check_infs tl else check_infs (!geq@tl) in check_infs [node]) sup) then (ps_of_set ([],None,[]) set; assert false);
);
    let set =
     locate_using_geq (to_be_considered,Some repr,news) node set start_inf
    in
(
let _,inf,sup = set in
if not (List.for_all (fun ((_,_,_,geq) as node) -> !geq = [] && let rec check_sups = function [] -> true | (_,_,leq,_) as node::tl -> if !leq = [] then List.exists (fun n -> n===node) sup && check_sups tl else check_sups (!leq@tl) in check_sups [node]) inf) then (ps_of_set ([],None,[]) set; assert false);
if not (List.for_all (fun ((_,_,leq,_) as node) -> !leq = [] && let rec check_infs = function [] -> true | (_,_,_,geq) as node::tl -> if !geq = [] then List.exists (fun n -> n===node) inf && check_infs tl else check_infs (!geq@tl) in check_infs [node]) sup) then ((*ps_of_set ([],None,[]) set;*) assert false);
);
     news@[candidate],set
   with
    SameEquivalenceClass ((nodes,inf,sup) as set,((r,_,leq_d,geq_d) as node_to_be_deleted),node')->
(
let _,inf,sup = set in
if not (List.for_all (fun ((_,_,_,geq) as node) -> !geq = [] && let rec check_sups = function [] -> true | (_,_,leq,_) as node::tl -> if !leq = [] then List.exists (fun n -> n===node) sup && check_sups tl else check_sups (!leq@tl) in check_sups [node]) inf) then (ps_of_set ([],None,[]) set; assert false);
if not (List.for_all (fun ((_,_,leq,_) as node) -> !leq = [] && let rec check_infs = function [] -> true | (_,_,_,geq) as node::tl -> if !geq = [] then List.exists (fun n -> n===node) inf && check_infs tl else check_infs (!geq@tl) in check_infs [node]) sup) then ((*ps_of_set ([],None,[]) set;*) assert false);
);
     let rec clean inf sup res =
      function
         [] -> inf,sup,res
       | node::tl when node===node_to_be_deleted ->
          clean inf sup res tl
       | (repr',others,leq,geq) as node::tl ->
          leq :=
           (let rec aux res =
             function
                [] -> res
              | (_,_,leq,_) as node::tl ->
                 if node_to_be_deleted <=> node then
                  aux (res@[node]) tl
                 else
                  (List.filter (fun n ->not (leq_reachable n (res@tl))) !leq)@tl
            in
             aux [] !leq);
          let sup = if !leq = [] then sup@@node else sup in
          geq :=
           (let rec aux res =
             function
                [] -> res
              | (_,_,_,geq) as node::tl ->
                 if node_to_be_deleted <=> node then
                  aux (res@[node]) tl
                 else
                  (List.filter (fun n ->not (geq_reachable n (res@tl))) !geq)@tl
            in
             aux [] !geq);
          let inf = if !geq = [] then inf@@node else inf in
          if node===node' then
           clean inf sup ((repr',others@[candidate],leq,geq)::res) tl
          else
           clean inf sup (node::res) tl
     in
     let inf,sup,nodes = clean inf sup [] nodes in
     let inf = remove node_to_be_deleted inf in
     let sup = remove node_to_be_deleted sup in
let set = nodes,inf,sup in
(
let _,inf,sup = set in
if not (List.for_all (fun ((_,_,_,geq) as node) -> !geq = [] && let rec check_sups = function [] -> true | (_,_,leq,_) as node::tl -> if !leq = [] then List.exists (fun n -> n===node) sup && check_sups tl else check_sups (!leq@tl) in check_sups [node]) inf) then (ps_of_set ([],None,[]) set; assert false);
if not (List.for_all (fun ((_,_,leq,_) as node) -> !leq = [] && let rec check_infs = function [] -> true | (_,_,_,geq) as node::tl -> if !geq = [] then List.exists (fun n -> n===node) inf && check_infs tl else check_infs (!geq@tl) in check_infs [node]) sup) then (ps_of_set ([],None,[]) set; assert false);
);
      news,(nodes,inf,sup)
;;

let rec explore i (set:set) news =
 let rec aux news set =
  function
     [] -> news,set
   | repr::tl ->
      let news,set =
       List.fold_right (analyze_one tl repr) [I;C;M] (news,set)
      in
       aux news set tl
 in
  let news,set = aux [] set news in
   if news = [] then
    begin
     print_endline ("PUNTO FISSO RAGGIUNTO! i=" ^ string_of_int i);
     print_endline (string_of_set set ^ "\n----------------");
     ps_of_set ([],None,[]) set
    end
   else
    begin
     print_endline ("NUOVA ITERAZIONE, i=" ^ string_of_int i);
     print_endline (string_of_set set ^ "\n----------------");
     explore (i+1) set news
    end
in
 let id = [] in
 let id_node = id,[],ref [], ref [] in
 let set = [id_node],[id_node],[id_node] in
  print_endline ("PRIMA ITERAZIONE, i=0, j=0");
  print_endline (string_of_set set ^ "\n----------------");
  (*ignore (Unix.system "rm -f log");*)
  assert (Unix.system "cp formal_topology.ma log.ma" = Unix.WEXITED 0);
  ps_of_set ([id],None,[]) set;
  explore 1 set [id]
;;
