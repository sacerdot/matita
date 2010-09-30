let _ = Helm_registry.load_from "extractor.conf.xml"

let usage () =
  prerr_endline "

!! This binary should not be called by hand, use the extractor_manager. !!

usage: ./extractor[.opt] path owner

path: the path for the getter maps
owner: the owner of the tables to update

"

let _ = 
  try
    let _ = Sys.argv.(2), Sys.argv.(1) in
    if Sys.argv.(1) = "-h"||Sys.argv.(1) = "-help"||Sys.argv.(1) = "--help" then
      begin
      usage ();
      exit 1
      end
  with 
    Invalid_argument _ -> usage (); exit 1

let owner = Sys.argv.(2)
let path = Sys.argv.(1)

let main () =
  print_endline (Printf.sprintf "%d alive on path:%s owner:%s" 
    (Unix.getpid()) path owner);
  Helm_registry.load_from "extractor.conf.xml";
  Helm_registry.set "tmp.dir" path;
  Http_getter.init ();
  let dbspec = LibraryDb.parse_dbd_conf () in
  let dbd = HSql.quick_connect dbspec in
  MetadataTypes.ownerize_tables owner;
  let uris =
    let ic = open_in (path ^ "/todo") in
    let acc = ref [] in
    (try
      while true do
        let l = input_line ic in
        acc := l :: !acc
      done
    with
      End_of_file -> ());
    close_in ic;
    !acc
  in
  let len = float_of_int (List.length uris) in
  let i = ref 0 in
  let magic = 45 in
  List.iter (fun u ->
    incr i;
    let perc = ((float_of_int !i)  /. len *. 100.0) in
    let l = String.length u in
    let short = 
      if l < magic then 
        u ^ String.make (magic + 3 - l) ' ' 
      else 
        "..." ^  String.sub u (l - magic) magic
    in
    Printf.printf "%d (%d of %.0f = %3.1f%%): %s\n" 
     (Unix.getpid ()) !i len perc short;
    flush stdout;
    let uri = UriManager.uri_of_string u in
    MetadataDb.index_obj ~dbd ~uri;
    CicEnvironment.empty ())
  uris;
  print_string "END "; Unix.system "date"
;;

main ()

