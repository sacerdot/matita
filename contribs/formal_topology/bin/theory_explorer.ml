type rel = Equal | SubsetEqual | SupersetEqual

let string_of_rel =
 function
    Equal -> "="
  | SubsetEqual -> "⊆"
  | SupersetEqual -> "⊇"

(* operator *)
type op = I | C | M

let string_of_op =
 function
    I -> "i"
  | C -> "c"
  | M -> "-"

(* compound operator *)
type compound_operator = op list

let string_of_cop op =
 if op = [] then "id" else String.concat "" (List.map string_of_op op)

let dot_of_cop op = "\"" ^ string_of_cop op ^ "\""

let rec matita_of_cop v =
 function
  | [] -> v
  | I::tl -> "i (" ^ matita_of_cop v tl ^ ")"
  | C::tl -> "c (" ^ matita_of_cop v tl ^ ")"
  | M::tl -> "m (" ^ matita_of_cop v tl ^ ")"

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

let test to_be_considered_and_now ((s,_,_) as set) rel candidate repr =
 ps_of_set to_be_considered_and_now ~processing:(candidate,rel,repr) set;
 print_string
  (string_of_cop candidate ^ " " ^ string_of_rel rel ^ " " ^ string_of_cop repr ^ "? ");
 flush stdout;
 assert (Unix.system "cp formal_topology.ma xxx.ma" = Unix.WEXITED 0);
 let ch = open_out_gen [Open_append] 0 "xxx.ma" in
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
  let candidate',rel',repr' =
   match rel with
      SupersetEqual -> repr,SubsetEqual,candidate
    | Equal
    | SubsetEqual -> candidate,rel,repr
  in
  output_string ch
   ("theorem foo: \\forall A." ^ matita_of_cop "A" candidate' ^
      " " ^ string_of_rel rel' ^ " " ^
      matita_of_cop "A" repr' ^ ". intros; auto size=6 depth=4. qed.\n");
  close_out ch;
  let res =
   (*Unix.system "../../../matitac.opt xxx.ma >> log 2>&1" = Unix.WEXITED 0*)
   Unix.system "../../../matitac.opt xxx.ma > /dev/null 2>&1" = Unix.WEXITED 0
  in
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

let locate_using_leq to_be_considered_and_now ((repr,_,leq,_) as node)
 set start
=
 let rec aux is_sup ((nodes,inf,sup) as set) =
  function
     [] ->
      if is_sup then
       nodes,inf,sup@@node
      else
       set
   | (repr',_,_,geq') as node' :: tl ->
       if repr=repr' then aux is_sup set (!geq'@tl)
       else if leq_reachable node' !leq then
        aux is_sup set tl
       else if test to_be_considered_and_now set SubsetEqual repr repr' then
        begin
         let inf = if !geq' = [] then (remove node' inf)@@node else inf in
          leq_transitive_closure node node';
          aux false (nodes,inf,sup) (!geq'@tl)
        end
       else
        aux is_sup set tl
 in
  aux true set start
;;

exception SameEquivalenceClass of equivalence_class * equivalence_class;;

let locate_using_geq to_be_considered_and_now ((repr,_,leq,geq) as node)
 set start
=
 let rec aux is_inf ((nodes,inf,sup) as set) =
  function
     [] ->
      if is_inf then
       nodes,inf@@node,sup
      else
       set
   | (repr',_,leq',_) as node' :: tl ->
       if repr=repr' then aux is_inf set (!leq'@tl)
       else if geq_reachable node' !geq then
        aux is_inf set tl
       else if test to_be_considered_and_now set SupersetEqual repr repr' then
        begin
         if List.exists (function n -> n===node') !leq then
          (* We have found two equal nodes! *)
          raise (SameEquivalenceClass (node,node'))
         else
          begin
           let sup = if !leq' = [] then (remove node' sup)@@node else sup in
            geq_transitive_closure node node';
            aux false (nodes,inf,sup) (!leq'@tl)
          end
        end
       else
        aux is_inf set tl
 in
  aux true set start
;;

let analyze_one to_be_considered repr hecandidate (news,((nodes,inf,sup) as set)) =
assert (List.for_all (fun (_,_,leq,geq) -> !geq = [] && let rec check_sups = function [] -> true | (_,_,leq,_) as node::tl -> if !leq = [] then List.exists (fun n -> n===node) sup && check_sups tl else check_sups (!leq@tl) in check_sups !leq) inf);
assert (List.for_all (fun (_,_,leq,geq) -> !leq = [] && let rec check_infs = function [] -> true | (_,_,_,geq) as node::tl -> if !geq = [] then List.exists (fun n -> n===node) inf && check_infs tl else check_infs (!geq@tl) in check_infs !geq) sup);
 let candidate = hecandidate::repr in
  if List.length (List.filter ((=) M) candidate) > 1 then
   news,set
  else
   try
    let leq = ref [] in
    let geq = ref [] in
    let node = candidate,[],leq,geq in
    let nodes = nodes@[node] in
    let set = nodes,inf,sup in
    let start_inf,start_sup =
     let repr_node =
      match List.filter (fun (repr',_,_,_) -> repr=repr') nodes with
         [node] -> node
       | _ -> assert false
     in
inf,sup(*
     match hecandidate with
        I -> inf,[repr_node]
      | C -> [repr_node],sup
      | M -> inf,sup
*)
    in
    let set =
     locate_using_leq (to_be_considered,Some repr,news) node set start_sup in
    let set =
     locate_using_geq (to_be_considered,Some repr,news) node set start_inf
    in
     news@[candidate],set
   with
    SameEquivalenceClass ((_,_,leq_d,geq_d) as node_to_be_deleted,node') ->
     let rec clean =
      function
         [] -> []
       | (repr',others,leq,geq) as node::tl ->
          leq :=
           List.fold_right
            (fun node l ->
              if node_to_be_deleted <=> node then
               node::l
              else
               !leq_d@l
            ) !leq [];
          geq :=
           List.fold_right
            (fun node l ->
              if node_to_be_deleted <=> node then
               node::l
              else
               !geq_d@l
            ) !geq [];
          if node===node' then
           (repr',others@[candidate],leq,geq)::clean tl
          else
           node::clean tl
     in
     let nodes = clean nodes in
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
  ps_of_set ([id],None,[]) set;
  explore 1 set [id]
;;
