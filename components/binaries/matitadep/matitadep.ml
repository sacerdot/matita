module StringSet = Set.Make (String) 

type file = {
   ddeps: string list;
   rdeps: StringSet.t option
}

let graph = Hashtbl.create 503

let rec purge dname bdeps = match bdeps with
   | []       -> bdeps
   | hd :: tl -> if hd = dname then bdeps else purge dname tl 

let add fname =
   if Hashtbl.mem graph fname then () else
   Hashtbl.add graph fname {ddeps = []; rdeps = None}

let add_ddep fname dname =
   let file = Hashtbl.find graph fname in
   Hashtbl.replace graph fname {file with ddeps = dname :: file.ddeps} 

let init fname dname =
   add fname; add dname; add_ddep fname dname 

let rec compute bdeps fname file = match file.rdeps with
   | Some rdeps -> rdeps
   | None       ->
      let bdeps = fname :: bdeps in
      let rdeps = List.fold_left (iter fname bdeps) StringSet.empty file.ddeps in
      Hashtbl.replace graph fname {file with rdeps = Some rdeps};
      rdeps

and iter fname bdeps rdeps dname =
   if StringSet.mem dname rdeps then begin
      Printf.printf "%s: redundant %s\n" fname dname;
      rdeps 
   end else if List.mem dname bdeps then begin
      let loop = purge dname (List.rev bdeps) in
      Printf.printf "circular: %s\n" (String.concat " " loop);
      StringSet.add dname rdeps
   end else
     let file = Hashtbl.find graph dname in
     StringSet.add dname (StringSet.union (compute bdeps dname file) rdeps)

let check () = 
   let iter fname file = ignore (compute [] fname file) in
   Hashtbl.iter iter graph 

let rec read ich = 
   let _ = Scanf.fscanf ich "%s@:include \"%s@\". " init in
   read ich
   
let _ =
   try read stdin with End_of_file -> check ()
