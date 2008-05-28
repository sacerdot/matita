
open Printf

exception Found of string list

let ocamlobjinfo = "ocamlobjinfo"
let noautolink = "-noautolink"
let dummy_opt_cmd = "dummy_ocamlopt"
let opt_cmd = "ocamlopt"
let libdirs = [ "/lib"; "/usr/lib"; "/usr/lib/gcc/i486-linux-gnu/4.0.2" ]
let exceptions = [ "threads.cma", [ "-lthreads", "-lthreadsnat" ] ]

let blanks_RE = Str.regexp "[ \t\r\n]+"
let cmxa_RE = Str.regexp "\\.cmxa$"
let extra_cfiles_RE = Str.regexp "^.*Extra +C +object +files:\\(.*\\)$"
let extra_copts_RE = Str.regexp "^.*Extra +C +options:\\(.*\\)$"
let lib_RE = Str.regexp "^lib"
let l_RE = Str.regexp "^-l"
let opt_line_RE = Str.regexp (sprintf "^\\+ +%s +\\(.*\\)$" dummy_opt_cmd)
let trailing_cmxa_RE = Str.regexp ".*\\.cmxa$"

let message s = prerr_endline ("STATIC_LINK: " ^ s)
let warning s = message ("WARNING: " ^ s)

let handle_exceptions ~cma cflag =
  try
    let cma_exns = List.assoc (Filename.basename cma) exceptions in
    let cflag' = List.assoc cflag cma_exns in
    message (sprintf "using %s exception %s -> %s" cma cflag cflag');
    cflag'
  with Not_found -> cflag

let parse_cmdline () =
  let mine, rest = ref [], ref [] in
  let is_mine = ref true in
  Array.iter
    (function
      | "--" -> is_mine := false
      | s when !is_mine ->
          if Str.string_match lib_RE s 0 then
            warning (sprintf
              ("libraries to be statically linked must be specified "
              ^^ "without heading \"lib\", \"%s\" argument may be wrong") s);
          mine := s :: !mine
      | s -> rest := s :: !rest)
    Sys.argv;
  if !rest = [] then begin
    prerr_endline "Usage:   static_link [ CLIB .. ] -- COMMAND [ ARG .. ]";
    prerr_endline ("Example: static_link pcre expat --"
      ^ " ocamlfind opt -package pcre,expat -linkpkg -o foo foo.ml");
    exit 0
  end;
  List.tl (List.rev !mine), List.rev !rest

let extract_opt_flags cmd =
  let ic = Unix.open_process_in cmd in
  (try
    while true do
      let l = input_line ic in
      if Str.string_match opt_line_RE l 0 then begin
        message ("got ocamlopt line: " ^ l);
        raise (Found (Str.split blanks_RE (Str.matched_group 1 l)));
      end
    done;
    []  (* dummy value *)
  with
  | End_of_file -> failwith "compiler command not found"
  | Found flags ->
      close_in ic;
      flags)

let cma_of_cmxa = Str.replace_first cmxa_RE ".cma"

let find_clib libname =
  let rec aux =
    function
    | [] -> raise Not_found
    | libdir :: tl ->
        let fname = sprintf "%s/lib%s.a" libdir libname in
        if Sys.file_exists fname then fname else aux tl
  in
  aux libdirs

let a_of_cflag cflag =  (* "-lfoo" -> "/usr/lib/libfoo.a" *)
  let libname = Str.replace_first l_RE "" cflag in
  find_clib libname

let cflags_of_cma fname =
  let ic = Unix.open_process_in (sprintf "%s %s" ocamlobjinfo fname) in
  let extra_copts = ref "" in
  let extra_cfiles = ref "" in
  (try
    while true do
      match input_line ic with
      | s when Str.string_match extra_copts_RE s 0 ->
          extra_copts := Str.matched_group 1 s
      | s when Str.string_match extra_cfiles_RE s 0 ->
          extra_cfiles := Str.matched_group 1 s
      | _ -> ()
    done
  with End_of_file -> ());
  close_in ic;
  let extra_cfiles = List.rev (Str.split blanks_RE !extra_cfiles) in
  let extra_copts = Str.split blanks_RE !extra_copts in
  extra_copts @ extra_cfiles

let staticize static_libs flags =
  let static_flags = List.map ((^) "-l") static_libs in
  let aux ~add_cclib ~cma cflag =
    let cflag =
      if List.mem cflag static_flags
      then
        (try
          let a = a_of_cflag cflag in
          message (sprintf "using static %s instead of shared %s" a cflag);
          a
        with Not_found -> warning ("can't find lib for " ^ cflag); cflag)
      else (handle_exceptions ~cma cflag)
    in
    if add_cclib then [ "-cclib"; cflag ] else [ cflag ]
  in
  List.fold_right
    (fun flag acc ->
      let cma = cma_of_cmxa flag in
      if Str.string_match trailing_cmxa_RE flag 0 then begin
        message ("processing native archive: " ^ flag);
        let cflags = cflags_of_cma cma in
        let cflags' =
          List.fold_right
            (fun cflag acc -> (aux ~add_cclib:true ~cma cflag) @ acc)
            cflags []
        in
        flag :: (cflags' @ acc)
      end else
        (aux ~add_cclib:false ~cma flag) @ acc)
    flags []

let quote_if_needed s =
  try
    ignore (Str.search_forward blanks_RE s 0);
    "\"" ^ s ^ "\""
  with Not_found -> s

let main () =
  let static_libs, args = parse_cmdline () in
  printf "C libraries to be linked-in: %s\n" (String.concat " " static_libs);
  flush stdout;
  let verbose_cmd =
    sprintf "OCAMLFIND_COMMANDS='ocamlopt=%s' %s -verbose 2>&1" dummy_opt_cmd
      (String.concat " " (List.map quote_if_needed args))
  in
  let orig_opt_flags = extract_opt_flags verbose_cmd in
  message ("original ocamlopt flags: " ^ String.concat " " orig_opt_flags);
  let opt_flags = staticize static_libs orig_opt_flags in
  message ("new ocamlopt flags: " ^ String.concat " " opt_flags);
  let flags = noautolink :: opt_flags in
  let cmd = String.concat " " (opt_cmd :: flags) in
  message ("executing command: " ^ cmd);
  exit (Sys.command cmd)

let _ = main ()

