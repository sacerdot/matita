module ET = MrcTypes
module RL = RecommLib

let read_substs substs ich =
  while true do
    let line = input_line ich in
    let subst = RL.split_on_char ',' line in
    substs := List.map (RL.split_on_char ' ') subst :: !substs
  done

let read_file file =
  let ich = open_in file in 
  let line = input_line ich in
  let scan r f d p o = r, f, d, p, o in
  let rmod, rfun, dmod, para, optn =
    Scanf.sscanf line "%s %s %S %b %b" scan
  in 
  let substs = ref [] in
  begin
    try read_substs substs ich with
    | End_of_file -> close_in ich
  end;
  {
     ET.cmod = Filename.remove_extension file; 
     rmod; rfun; dmod; para; optn;
     substs = !substs;
  } 

let list_rev_filter_map filter map l =
  let rec aux r = function
    | []       -> r 
    | hd :: tl -> if filter hd then aux (map hd :: r) tl else aux r tl  
  in
  aux [] l

let read_dir file =
  let filter name =
    Filename.extension name = ".mrc"
  in
  let map name =
    Filename.remove_extension name
  in
  let dir = Array.to_list (Sys.readdir file) in
  let mods = List.fast_sort Pervasives.compare (list_rev_filter_map filter map dir) in
  {
    ET.cdir = file; mods;
  }

let rec read_mods mods ich =
  let line = input_line ich in
  let scan _ m =
    mods := m :: !mods
  in
  Scanf.sscanf line "module %s = RecommGc%s" scan;
  read_mods mods ich

let read_index dir =
  let file = Filename.concat dir "recommGc.ml" in
  let mods = ref [] in
  if Sys.file_exists file then begin
    let ich = open_in file in
    try read_mods mods ich with
    | End_of_file -> close_in ich 
  end;
  let mods = List.fast_sort Pervasives.compare !mods in
  {
    ET.cdir = dir; mods;
  }
