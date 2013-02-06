module StringSet = Set.Make (String) 

type file = {
   ddeps: string list;
   rdeps: StringSet.t option
}

let graph = Hashtbl.create 503

let add fname =
   if Hashtbl.mem graph fname then () else
   Hashtbl.add graph fname {ddeps = []; rdeps = None}

let add_ddep fname dname =
   let file = Hashtbl.find graph fname in
   Hashtbl.replace graph fname {file with ddeps = dname :: file.ddeps} 

let init fname dname =
   add fname; add dname; add_ddep fname dname 

let rec compute fname file = match file.rdeps with
   | Some rdeps -> rdeps
   | None       ->
      let rdeps = List.fold_left (iter fname) StringSet.empty file.ddeps in
      Hashtbl.replace graph fname {file with rdeps = Some rdeps};
      rdeps

and iter fname rdeps dname =
   if StringSet.mem dname rdeps then
      begin Printf.printf "%s: redundant %s\n" fname dname; rdeps end
   else
     let file = Hashtbl.find graph dname in
     StringSet.add dname (StringSet.union (compute dname file) rdeps)

let check () = 
   let iter fname file = 
      if StringSet.mem fname (compute fname file) then
         Printf.printf "%s: circular\n" fname 
   in
   Hashtbl.iter iter graph 

let rec read ich = 
   let _ = Scanf.fscanf ich "%s@:include \"%s@\". " init in
   read ich
   
let _ =
   try read stdin with End_of_file -> check ()
