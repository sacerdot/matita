(* 0: 7       4    0.312    3 5 7
   1: 29      6    0.549    3 8 16 24 29
   2: 120    10   25.525    3 8 19 39 66  95 113 119 120
   3: > 327  >9             3 8 19 39 75 134 208 274
   4: > 657  >9             3 8 19 39 75 139 245
   5: > 526  >8             3 8 19 39 75 139 245
   6: > 529  >8
   7: > 529  >8
   8: > 529  >8

(CMM?)+ | (MM?C)+

cCw = Cw
-Cw = MCw
cMw = CMw
-MMw = -w
-MCw = MMCw
iw = w


  s <= s'            s <= s'         s <= s'           s <= s'
===========        ===========     ============      ==========
 ws <= Cws'         Cs <= Cs'       CMs' <= Ms       Ms' <= MCs

  s <= s'          s <= s'
===========     ============
 s <= MMs'        Ms' <= Ms

*)

type t = M | I | C
type w = t list
type eqclass = w list

type dir = Le | Ge

let rules =
 [ [I],     Le, [];
   [C],     Ge, [];
   [I;I],   Ge, [I];
   [C;C],   Le, [C];
   [I],     Le, [I];
   [I],     Ge, [I];
   [C],     Le, [C];
   [C],     Ge, [C];
   [C;M],   Le, [M;I];
   [C;M;I], Le, [M;I];  (* ??? *)
   [I;M],   Le, [M;C];
   [I;M;C], Ge, [I;M];  (* ??? *)
   [M;M;M], Ge, [M];
   [M;M],   Ge, [];
   [M],     Le, [M];
   [M],     Ge, [M];
   (* classical
   [M;M],   Le, [];
   [C;M],   Ge, [M;I];
   *)
 ]
;;

let inject =
 let cache = Hashtbl.create 5393 in
 function w ->
  try
   Hashtbl.find cache w
  with
   Not_found ->
    let rec aux acc =
     function
        [] -> acc
      | he::tl -> aux (4 * acc + (match he with I -> 1 | C -> 2 | M -> 3)) tl
    in
     let res = 0, aux 0 w, w in
      Hashtbl.add cache w res;
      res
;;

module VL =
 struct
  type t = eqclass
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
 end

module GL = Graph.Imperative.Digraph.Concrete(VL);;

let swap = function Le -> Ge | Ge -> Le;;

let rec new_dir dir =
 function
    [] -> dir
  | M::tl -> new_dir (swap dir) tl
  | (C|I)::tl -> new_dir dir tl
;;

let string_of_w w =
 let s =
  String.concat ""
   (List.map (function I -> "i" | C -> "c" | M -> "-") w)
 in
  if s = "" then "." else s
;;

let string_of_w' w =
 let s =
  String.concat ""
   (List.map (function I -> "i" | C -> "c" | M -> "m") w)
 in
  if s = "" then "E" else s
;;

let string_of_eqclass l = String.concat "=" (List.map string_of_w l);;

let name_of_eqclass l = String.concat "_" (List.map string_of_w' l);;

exception NoMatch;;

let (@@) l1 ll2 = List.map (function l2 -> l1 @ l2) ll2;;

let uniq l =
 let rec aux acc = function
  | [] -> acc
  | h::[] -> h::acc
  | h1::h2::tl when h1=h2 -> aux (h2::acc) tl
  | h1::tl (* when h1 <> h2 *) -> aux (h1::acc) tl
 in
  List.rev (aux [] (List.sort compare l))
;;

let rec apply_rule_at_beginning (lhs,dir',rhs) (w,dir) =
 if dir <> dir' then
  raise NoMatch
 else
  let rec aux =
   function
      [],w -> w
    | x::lhs,x'::w when x = x' -> aux (lhs,w)
    | _,_ -> raise NoMatch in
  let w' = aux (lhs,w) in
   if List.length rhs < List.length lhs then rhs @@ [w']
   else rhs @@ apply_rules (aux (lhs,w),new_dir dir lhs)
and apply_rules (w,_ as w_and_dir) =
 if w = [] then [[]]
 else
  let rec aux =
   function
      [] -> []
    | rule::tl ->
       (try apply_rule_at_beginning rule w_and_dir
        with NoMatch -> [])
       @
       aux tl
  in
   aux rules
;;

let apply_rules (w,dir as w_and_dir) =
 List.map (fun w' -> w,dir,w')
  (uniq (apply_rules w_and_dir))
;;

let step (l : w list) =
 uniq
  (List.flatten
    (List.map
     (function w ->
       List.map (fun x -> x@w)
       (if List.length (List.filter (fun w -> w = M) w) >= 5 then
         [[I];[C]]
        else
         [[I];[C];[M]])
     ) l))
;;

let mapi f l =
 let rec aux acc i =
  function
     [] -> acc
   | he::tl ->
      if i mod 1000 = 0 then
       begin
        print_string ("@" ^ string_of_int i ^ " ");
        flush stdout;
       end;
      aux (f he :: acc) (i+1) tl
 in
  let res = List.rev (aux [] 1 l) in
   print_newline ();
   res
;;

let iteri f l =
 let rec aux i =
  function
     [] -> ()
   | he::tl ->
      if i mod 1000 = 0 then
       begin
        print_string ("@" ^ string_of_int i ^ " ");
        flush stdout;
       end;
      f he; aux (i+1) tl
 in
  aux 1 l;
  print_newline ();
;;

let normalize canonical (l : w list) =
 print_endline (string_of_int (List.length l) ^ " nodes to be normalized");
 let rec aux all l =
  let rels =
   List.flatten
    (mapi (fun x -> apply_rules (x,Le) @ apply_rules (x,Ge)) l) in
  let arcs =
   mapi
    (function (x,rel,y) ->
      let x = canonical x(*(inject x)*) in
      let y = canonical y(*(inject y)*) in
       match rel with Le -> x,y | Ge -> y,x) rels in
  let res = uniq arcs in
  let nodes = uniq (l @ List.map (fun (_,_,n) -> n) rels) in
  let new_nodes = List.filter (fun n -> not (List.mem n all)) nodes in
  let new_nodes = List.filter (function n -> [n] = canonical n) new_nodes in
   if new_nodes = [] then
    res
   else
    uniq (res @ aux nodes new_nodes)
 in
  aux l l
;;

let visualize graph =
 let module GL =
  struct
   include GL;;
   let edge_attributes _ = []
   let default_edge_attributes _ = []
   let get_subgraph _ = None
   let vertex_attributes v = [`Label (string_of_eqclass (GL.V.label v))]
   let vertex_name v = name_of_eqclass (GL.V.label v)
   let default_vertex_attributes _ = []
   let graph_attributes _ = []
  end in
 let module D = Graph.Graphviz.Dot(GL) in
  let ch = open_out "/tmp/comb.dot" in
   D.output_graph ch graph;
   close_out ch;
   ignore (Unix.system ("tred /tmp/comb.dot > /tmp/red.dot"));
   ignore (Unix.system ("dot -Tps /tmp/red.dot > /tmp/red.ps"));
   (*Unix.system ("ggv /tmp/red.ps");*)
;;

let w_compare s1 s2 =
 let c = compare (List.length s1) (List.length s2) in
  if c = 0 then compare s1 s2 else c
;;

exception Found of GL.V.t;;

let rec iter n cgraph (canonical: w -> GL.V.t) =
 print_endline ("STEP " ^ string_of_int n);
 let nodes = GL.fold_vertex (fun n l -> n::l) cgraph [] in
 let nodes = step (List.map List.hd nodes) in
(*let nodes = [[C;M];[C;M;C;M];[C;M;C;M;C;M];[C;M;C;M;C;M;C;M];[C;M;C;M;C;M;C;M;C;M]] in*)
(*let nodes = [[C;I;C;I;C;I]] in*)
 (*let nodes = step (List.concat nodes) in*)
(*List.iter (fun x -> prerr_endline ("#@ " ^ string_of_w x)) nodes;*)
 let arcs = normalize canonical nodes in
  iteri (fun (x,y) -> if x <> y then GL.add_edge cgraph x y) arcs;
(*List.iter (fun (x,y) -> prerr_endline (string_of_eqclass x ^ " -> " ^ string_of_eqclass y)) arcs;*)

  print_endline ("<scc>");
  let classes,norm =
   let module SCC = Graph.Components.Make(GL) in SCC.scc cgraph in
  let xxx =
   let module SCC = Graph.Components.Make(GL) in SCC.scc_array cgraph in
  print_endline ("</scc>");
  let get_canonical n =
   try List.sort w_compare (List.concat (xxx.(norm n)))
   with Not_found -> n
  in
  let nodes = GL.fold_vertex (fun n l -> n::l) cgraph [] in
  print_endline "get_canonical";
  let nodes = mapi (fun n -> n,get_canonical n) nodes in
  print_endline "/get_canonical";
  print_endline ("collapse " ^ string_of_int (List.length nodes));
  iteri
   (function (n,n') ->
     let succ = GL.succ cgraph n in
     let pred = GL.pred cgraph n in
      GL.remove_vertex cgraph n;
      let add_edge s t = if s <> t then GL.add_edge cgraph s t in
      List.iter (fun s -> add_edge n' (get_canonical s)) succ;
      List.iter (fun p -> add_edge (get_canonical p) n') pred)
   nodes;
  print_endline (string_of_int classes ^ " classes");
  print_endline ("-----");
  print_endline "visualize";
  visualize cgraph;
  print_endline ("/////");
  GL.iter_vertex (fun l -> print_endline ("?" ^ string_of_eqclass l)) cgraph;
  let canonical =
   function (*_,_,*)w ->
    try
     GL.iter_vertex (fun l -> if List.mem w l then raise (Found l)) cgraph;
     [w]
    with
     Found l -> l in
  if n > 0 then
   iter (n - 1) cgraph canonical
  else
   ()
in
 let cgraph = GL.create () in
  GL.add_vertex cgraph [[]];
  iter 9 cgraph (fun w(*(_,_,w)*) -> [w])
;;
