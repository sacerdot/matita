module StringSet = Set.Make (String)

type file = {
  ddeps: string list;        (* direct dependences *)
  rdeps: StringSet.t option  (* recursive dependences *)
}

let show_check = ref false
let show_top = ref false
let show_leaf = ref false
let show_back = ref ""
let iset = ref StringSet.empty

let graph = Hashtbl.create 503

let debug = ref 0

let rec purge dname vdeps = match vdeps with
  | []       -> vdeps
  | hd :: tl -> if hd = dname then tl else hd :: purge dname tl

let add fname =
  if fname = "" then () else
  if Hashtbl.mem graph fname then () else
  Hashtbl.add graph fname {ddeps = []; rdeps = None}

let add_ddep fname dname =
  if dname = "" then () else
  let file = Hashtbl.find graph fname in
  Hashtbl.replace graph fname {file with ddeps = dname :: file.ddeps}

let init fname dname =
  if !debug land 1 > 0 then Printf.printf "init: %s: %s.\n" fname dname;
  add fname; add dname; add_ddep fname dname

(* vdeps: visited dependences for loop detection *)
let rec compute_from_file vdeps fname file = match file.rdeps with
  | Some rdeps -> rdeps
  | None       ->
    if !debug land 2 > 0 then Printf.printf "  (%u) compute object: %s\n%!" (List.length vdeps) fname;
    if !debug land 2 > 0 then Printf.printf "  ddeps: %s\n%!" (String.concat " " file.ddeps);
    if !debug land 8 > 0 then Printf.printf "  vdeps: %s\n%!" (String.concat " " vdeps);
    if List.mem fname vdeps then begin
      if !show_check then Printf.printf "circular: %s\n%!" (String.concat " " vdeps);
      StringSet.empty
    end else begin
      let vdeps = fname :: vdeps in
      List.iter (redundant vdeps fname file.ddeps) file.ddeps;
      let rdeps = compute_from_ddeps vdeps file.ddeps in
      Hashtbl.replace graph fname {file with rdeps = Some rdeps};
      rdeps
    end

and compute_from_dname vdeps rdeps dname =
  if !debug land 4 > 0 then Printf.printf "  (%u) compute dep: %s\n%!" (List.length vdeps) dname;
  if !debug land 8 > 0 then Printf.printf "  vdeps: %s\n%!" (String.concat " " vdeps);
  let file = Hashtbl.find graph dname in
  let rdeps = StringSet.add dname rdeps in
  StringSet.union (compute_from_file vdeps dname file) rdeps

and compute_from_ddeps vdeps ddeps =
  List.fold_left (compute_from_dname vdeps) StringSet.empty ddeps

and redundant vdeps fname ddeps dname =
  let rdeps = compute_from_ddeps vdeps (purge dname ddeps) in
  if !show_check && StringSet.mem dname rdeps then
    Printf.printf "%S: redundant %S\n%!" fname dname

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

let rec file_iter map ich =
  let line = input_line ich in
  if line <> "" then map line;
  file_iter map ich

let back name =
  Printf.printf "\"%s\":\n" name;
  try match (Hashtbl.find graph name).rdeps with
    | None       -> ()
    | Some rdeps ->
      let rdeps =
        if !iset = StringSet.empty then rdeps
        else StringSet.inter rdeps !iset
      in
      let iter name = Printf.printf "  \"%s\"\n" name in
      StringSet.iter iter rdeps;
      Printf.printf "\n"
  with Not_found -> Printf.printf "* not found\n\n"

let back fname =
  if Librarian.is_uri fname then back fname else
  let ich = open_in fname in
  try file_iter back ich with End_of_file -> close_in ich

let set_iset fname =
  if Librarian.is_uri fname then iset := StringSet.singleton fname else
  let map name = iset := StringSet.add name !iset in
  let ich = open_in fname in
  try file_iter map ich with End_of_file -> close_in ich

let rec read_many ich s =
  let line = input_line ich in
  if line = "" then () else begin
    begin try Scanf.sscanf line " %S" (init s)
    with Scanf.Scan_failure _ | End_of_file ->
      Printf.eprintf "unknown line: %s.\n" line
    end;
    read_many ich s
  end

let rec read_deps ich =
  let line = input_line ich in
  begin try Scanf.sscanf line "%s@:include %S." init
  with Scanf.Scan_failure _ | End_of_file ->
    begin try Scanf.sscanf line "./%s@:include %S." init
    with Scanf.Scan_failure _ | End_of_file ->
      begin try Scanf.sscanf line "%s@:(*%s@*)" (fun _ _ -> ())
      with Scanf.Scan_failure _ | End_of_file ->
        begin try Scanf.sscanf line "%S:%!" (read_many ich)
        with Scanf.Scan_failure _ | End_of_file ->
          begin try Scanf.sscanf line "%S: %S" init
          with Scanf.Scan_failure _ | End_of_file ->
            Printf.eprintf "unknown line: %s.\n" line
          end
        end
      end
    end
  end;
  read_deps ich

let _ =
  let process_file name =
    let ich = open_in name in
    try read_deps ich with End_of_file -> close_in ich
  in
  let show () =
    if !show_check || !show_back <> "" then check ();
    if !show_top then top ();
    if !show_leaf then leaf ();
    if !show_back <> "" then back !show_back
  in
  let help   = "matitadep [ -clt | -d <int> | -bi [ <uri> | <file> ] | <file> ]*" in
  let help_b = "<uri>|<file>  Print the backward dependences of these nodes" in
  let help_c = " Print the redundant and looping arcs of the dependences graph" in
  let help_d = "<flags>  Set these debug options" in
  let help_i = "<uri>|<file>  Intersect with these nodes" in
  let help_l = " Print the leaf nodes of the dependences graph" in
  let help_t = " Print the top nodes of the dependences graph" in
  Arg.parse [
    "-b", Arg.String ((:=) show_back), help_b;
    "-c", Arg.Set show_check, help_c;
    "-d", Arg.Int ((:=) debug), help_d;
    "-i", Arg.String set_iset, help_i;
    "-l", Arg.Set show_leaf, help_l;
    "-t", Arg.Set show_top, help_t;
  ] process_file help;
  show ()
