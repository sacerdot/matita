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

let string_of_equivalence_class (repr,others,leq,_) =
 String.concat " = " (List.map string_of_cop (repr::others)) ^
  (if !leq <> [] then
    "\n" ^
     String.concat "\n" 
      (List.map
        (function (repr',_,_,_) ->
           string_of_cop repr ^ " <= " ^ string_of_cop repr') !leq)
   else
    "")

let dot_of_equivalence_class (repr,others,leq,_) =
 (if others <> [] then
   let eq = String.concat " = " (List.map string_of_cop (repr::others)) in
    string_of_cop repr ^ "[label=\"" ^ eq ^ "\"];\n"
  else "") ^
   String.concat "\n" 
    (List.map
      (function (repr',_,_,_) ->
         string_of_cop repr' ^ " -> " ^ string_of_cop repr ^ ";") !leq)

(* set of equivalence classes *)
type set = equivalence_class list

let string_of_set s =
 String.concat "\n" (List.map string_of_equivalence_class s)

let ps_of_set ?processing s =
 let ch = open_out "xxx.dot" in
  output_string ch "digraph G {\n";
  output_string ch (String.concat "\n" (List.map dot_of_equivalence_class s));
  (match processing with
      None -> ()
    | Some (repr,rel,repr') ->
       output_string ch
        (string_of_cop repr' ^ " -> " ^ string_of_cop repr ^
         " [" ^
         (if rel="=" then "arrowhead=none " else "") ^
         "style=dashed];\n"));
  output_string ch "}\n";
  close_out ch;
  ignore (Unix.system "dot -Tps xxx.dot > xxx.ps")

let test set rel candidate repr =
 ps_of_set ~processing:(candidate,rel,repr) set;
 print_string
  (string_of_cop candidate ^ " " ^ rel ^ " " ^ string_of_cop repr ^ "? ");
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
   ) set;
  output_string ch
   ("theorem foo: \\forall A." ^ matita_of_cop "A" candidate ^ " " ^ rel ^ " " ^
     matita_of_cop "A" repr ^ ". intros; auto size=6 depth=4. qed.\n");
  close_out ch;
  let res =
   Unix.system "../../../matitac.opt xxx.ma >> log 2>&1" = Unix.WEXITED 0
  in
   print_endline (if res then "y" else "n");
   res

let normalize candidate set =
 let rec aux =
  function
     [] -> raise Not_found
   | (repr,others,leq,geq) as eqclass :: tl ->
       if test set "=" candidate repr then
        (repr,others@[candidate],leq,geq)::tl
       else
        eqclass::(aux tl) 
 in
  aux set
;;

let locate ((repr,_,leq,geq) as node) set =
 let rec aux =
  function
     [] -> ()
   | (repr',_,leq',geq') as node' :: tl ->
       if repr = repr' then ()
       else if test set "⊆" repr repr' then
        begin
         leq  := node' :: !leq;
         geq' := node  :: !geq'
        end
       else if test set "⊆" repr' repr then
        begin
         geq  := node' :: !geq;
         leq' := node  :: !leq'
        end ;
       aux tl
 in
  aux set
;;

let analyze_one i repr hecandidate (news,set) =
 let candidate = hecandidate::repr in
  if List.length (List.filter ((=) M) candidate) > i then
   news,set
  else
   try
    let set = normalize candidate set in
     news,set
   with
    Not_found ->
     let leq = ref [] in
     let geq = ref [] in
     let node = candidate,[],leq,geq in
     let set = node::set in
      locate node set;
      candidate::news,set
;;

let rec explore i j set news =
 let rec aux news set =
  function
     [] -> news,set
   | repr::tl ->
      let news,set =
       List.fold_right (analyze_one i repr) [I;C;M] (news,set)
      in
       aux news set tl
 in
  let news,set = aux [] set news in
   if news = [] then
    begin
     print_endline ("PUNTO FISSO RAGGIUNTO! i=" ^ string_of_int i ^ " j=" ^ string_of_int j);
     print_endline (string_of_set set ^ "\n----------------");
     if i < 2 then
      explore (i+1) 1 set (List.map (function (repr,_,_,_) -> repr) set)
     else
      ps_of_set set
    end
   else
    begin
     print_endline ("NUOVA ITERAZIONE, i=" ^ string_of_int i ^ " j=" ^ string_of_int j);
     print_endline (string_of_set set ^ "\n----------------");
     explore i (j+1) set news
    end
in
 let id = [] in
 let set = [id,[],ref [], ref []] in
  print_endline ("PRIMA ITERAZIONE, i=0, j=0");
  print_endline (string_of_set set ^ "\n----------------");
  ignore (Unix.system "rm -f log");
  ps_of_set set;
  explore 0 1 set [id]
;;
