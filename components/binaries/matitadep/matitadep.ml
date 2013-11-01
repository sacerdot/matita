module StringSet = Set.Make (String) 

type file = {
   ddeps: string list;        (* direct dependences *)
   rdeps: StringSet.t option  (* recursive dependences *)
}

let graph = Hashtbl.create 503

let debug = ref 0

let rec purge dname vdeps = match vdeps with
   | []       -> vdeps
   | hd :: tl -> if hd = dname then tl else hd :: purge dname tl 

let add fname =
   if Hashtbl.mem graph fname then () else
   Hashtbl.add graph fname {ddeps = []; rdeps = None}

let add_ddep fname dname =
   let file = Hashtbl.find graph fname in
   Hashtbl.replace graph fname {file with ddeps = dname :: file.ddeps} 

let init fname dname =
   if !debug land 1 > 0 then Printf.eprintf "init: %s: %s.\n" fname dname;
   add fname; add dname; add_ddep fname dname 

(* vdeps: visited dependences for loop detection *)
let rec compute_from_file vdeps fname file = match file.rdeps with
   | Some rdeps -> rdeps
   | None       ->   
      if !debug land 2 > 0 then Printf.eprintf "  compute file: %s\n" fname; 
      let vdeps = fname :: vdeps in
      List.iter (redundant vdeps fname file.ddeps) file.ddeps;
      let rdeps = compute_from_ddeps vdeps file.ddeps in
      Hashtbl.replace graph fname {file with rdeps = Some rdeps};      
      rdeps

and compute_from_dname vdeps rdeps dname =
   if List.mem dname vdeps then begin
      let loop = purge dname (List.rev vdeps) in
      Printf.printf "circular: %s\n" (String.concat " " loop);
      StringSet.add dname rdeps
   end else
     let file = Hashtbl.find graph dname in
     StringSet.add dname (StringSet.union (compute_from_file vdeps dname file) rdeps)

and compute_from_ddeps vdeps ddeps = 
   List.fold_left (compute_from_dname vdeps) StringSet.empty ddeps

and redundant vdeps fname ddeps dname =
   let rdeps = compute_from_ddeps vdeps (purge dname ddeps) in
   if StringSet.mem dname rdeps then
      Printf.printf "%s: redundant %s\n" fname dname

let check () = 
   let iter fname file = ignore (compute_from_file [] fname file) in
   Hashtbl.iter iter graph 

let get_unions () =
   let map1 ddeps dname = StringSet.add dname ddeps in 
   let map2 fname file (fnames, ddeps) =
      StringSet.add fname fnames, List.fold_left map1 ddeps file.ddeps
   in
   Hashtbl.fold map2 graph (StringSet.empty, StringSet.empty)

let get_leafs () =
   let map fname file fnames =
      if file.ddeps = [] then StringSet.add fname fnames else fnames
   in
   Hashtbl.fold map graph StringSet.empty

let top () =
   let iter fname = Printf.printf "top: %s\n" fname in
   let fnames, ddeps = get_unions () in
   StringSet.iter iter (StringSet.diff fnames ddeps) 

let leaf () =
   let iter fname = Printf.printf "leaf: %s\n" fname in
   let fnames = get_leafs () in
   StringSet.iter iter fnames

let rec read ich = 
   let line = input_line ich in
   begin try Scanf.sscanf line "%s@:include \"%s@\"." init 
   with Scanf.Scan_failure _ ->
      begin try Scanf.sscanf line "./%s@:include \"%s@\"." init
      with Scanf.Scan_failure _ ->   
         begin try Scanf.sscanf line "%s@:(*%s@*)" (fun _ _ -> ())
         with Scanf.Scan_failure _ ->
	    Printf.eprintf "unknown line: %s.\n" line
         end
      end  
   end;
   read ich
   
let _ =
   let show_check = ref false in
   let show_top = ref false in
   let show_leaf = ref false in   
   let process_file name = () in
   let show () =
      if !show_check then check ();
      if !show_top then top ();
      if !show_leaf then leaf ()   
   in
   let help   = "" in
   let help_c = " Print the redundant and looping arcs of the dependences graph" in
   let help_d = "<flags>  Set these debug options" in
   let help_l = " Print the leaf nodes of the dependences graph" in
   let help_t = " Print the top nodes of the dependences graph" in
   Arg.parse [
      "-c", Arg.Set show_check, help_c;
      "-d", Arg.Int (fun x -> debug := x), help_d;
      "-l", Arg.Set show_leaf, help_l;
      "-t", Arg.Set show_top, help_t;
   ] process_file help;
   try read stdin with End_of_file -> show ()
