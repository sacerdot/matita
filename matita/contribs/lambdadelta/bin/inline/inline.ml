module Deps  = Set.Make(String)
module Table = Map.Make(String)

let opt_map f = function
  | None   -> None
  | Some a -> Some (f a)

let rec filename_split l s =
  let dir, base = Filename.dirname s, Filename.basename s in
  if dir = Filename.current_dir_name then base::l else filename_split (base::l) dir

let filename_concat l =
  String.concat Filename.dir_sep l

let relative s =
  match filename_split [] s with
  | "cic:" :: "matita" :: "lambdadelta" :: tl -> List.rev tl
  | _                                         -> []

let to_string l =
  filename_concat (List.rev l)

let table = ref (Table.empty: Deps.t Table.t) 

let add src dep =
  let deps = match Table.find_opt src !table with
  | None      -> Deps.singleton dep
  | Some deps -> Deps.add dep deps
  in
  table := Table.add src deps !table

let split_or s =
  let map m = Printf.sprintf "or_%u" m in 
  try Scanf.sscanf s "or%u" map
  with Scanf.Scan_failure _ | End_of_file -> ""

let split_and s =
  let map m = Printf.sprintf "and_%u" m in 
  try Scanf.sscanf s "and%u" map
  with Scanf.Scan_failure _ | End_of_file -> ""

let split_ex s =
  let map m n = Printf.sprintf "ex_%u_%u" m n in 
  try Scanf.sscanf s "ex%u=%u" map
  with Scanf.Scan_failure _ | End_of_file -> ""

let split_ex1 s =
  let map m = Printf.sprintf "ex_%u_1" m in 
  try Scanf.sscanf s "ex%u" map
  with Scanf.Scan_failure _ | End_of_file -> ""

let map_deps s1 s2 =
  match relative s2 with
  | [b2;"xoa";"xoa";"ground_2"] ->
    let r1 = List.tl (relative s1) in
    let r1 = to_string r1 in
    let b2 = Filename.remove_extension b2 in
(* '_' is accepted (and ignored) within integer literals *)
    let b2 = String.concat "=" (String.split_on_char '_' b2) in
    let r2 =
      let cx = split_ex b2 in
      let cy = split_ex1 b2 in
      let ca = split_and b2 in
      let co = split_or b2 in
      if cx <> "" then cx else
      if cy <> "" then cy else
      if ca <> "" then ca else
      if co <> "" then co else
      failwith (Printf.sprintf "unrecognized xoa: %S\n" b2)
    in
    if r1 <> "ground_2/xoa/xoa" then add r1 r2
  | _                           -> ()

let reds = ref []

let map_reds s1 s2 =
  reds := (s1,s2) :: !reds

let rec read map_deps map_reds ich =
  let line = input_line ich in
  begin try Scanf.sscanf line "%S: %S" map_deps
  with Scanf.Scan_failure _ | End_of_file ->
    begin try Scanf.sscanf line "%S: redundant %S" map_reds
    with Scanf.Scan_failure _ | End_of_file ->
      Printf.eprintf "unknown line: %s.\n" line
    end
  end; 
  read map_deps map_reds ich

let xoadir = ref "ground_2/xoa"

let print_deps () =
  let map_d src dep =
    let src = src^".ma" in
    let dep = Filename.concat !xoadir (dep^".ma") in
    if List.mem (src,dep) !reds then ()
    else Printf.printf "%S: %S\n" src dep
  in
  let map_t src deps =
    Deps.iter (map_d src) deps
  in
  Table.iter map_t !table

let rec copy xn ich och =
  if xn = Some 0 then ()
  else begin
    Printf.fprintf och "%s\n" (input_line ich); 
    copy (opt_map pred xn) ich och
  end

let base_dir = ref ""

let preamble = ref 14

let insert_deps () =
  let map_d src dep rdeps =
    let dep = Filename.concat !xoadir (dep^".ma") in
    if List.mem (src,dep) !reds then rdeps else dep::rdeps
  in
  let map_r och rdep =
    Printf.fprintf och "include %S.\n" rdep;
  in
  let map_t src deps =
    let src = src^".ma" in
    let rdeps = Deps.fold (map_d src) deps [] in
    if rdeps <> [] then begin    
      let ma = Filename.concat !base_dir src in
      let old = ma^".old" in
      Sys.rename ma old;
      let och = open_out ma in
      let ich = open_in old in
      copy (Some !preamble) ich och;
      List.iter (map_r och) (List.rev rdeps);
      try copy None ich och
      with End_of_file -> close_in ich; close_out och
    end 
  in
  Table.iter map_t !table

let process fname =
  let ich = open_in fname in
  try read map_deps map_reds ich with 
  | End_of_file -> close_in ich

let help_b = "<dir>  Set this base directory (default: current directory)"
let help_i = "  Insert the dependences (default: no)"
let help_l = "<int>  .ma preamble has theese lines (default: 14)"
let help_p = "  Print the dependences to be inserted (default: no)"
let help = "inline [ -ip | -b <dir> | -l <int> | <file> ]*"

let print = ref false
let insert = ref false

let _ =
  Arg.parse [
    "-b", Arg.String ((:=) base_dir), help_b;
    "-l", Arg.Int ((:=) preamble), help_l;
    "-i", Arg.Set insert, help_i; 
    "-p", Arg.Set print, help_p; 
  ] process help;
  if !print then print_deps ();
  if !insert then insert_deps ()
