(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

let debug = ref 0

let time_stamp =
   let old = ref 0.0 in
   fun msg -> 
      if !debug > 0 then begin
         let times = Unix.times () in
         let stamp = times.Unix.tms_utime +. times.Unix.tms_stime in
         let lap = stamp -. !old in
         Printf.eprintf "TIME STAMP (%s): %f\n" msg lap; flush stderr;
         old := stamp
      end

exception NoRootFor of string

let absolutize path =
 let path = 
   if String.length path > 0 && path.[0] <> '/' then
     Sys.getcwd () ^ "/" ^ path
   else 
     path
 in
   HExtlib.normalize_path path
;;


let find_root path =
  let path = absolutize path in
  let paths = List.rev (Str.split (Str.regexp "/") path) in
  let rec build = function
    | he::tl as l -> ("/" ^ String.concat "/" (List.rev l) ^ "/") :: build tl
    | [] -> ["/"]
  in
  let paths = List.map HExtlib.normalize_path (build paths) in
  try HExtlib.find_in paths "root"
  with Failure "find_in" -> 
    raise (NoRootFor (path ^ " (" ^ String.concat ", " paths ^ ")"))
;;
  
let ensure_trailing_slash s = 
  if s = "" then "/" else
  if s.[String.length s-1] <> '/' then s^"/" else s
;;

let remove_trailing_slash s = 
  if s = "" then "" else
  let len = String.length s in
  if s.[len-1] = '/' then String.sub s 0 (len-1) else s
;;

let load_root_file rootpath =
  let data = HExtlib.input_file rootpath in
  let lines = Str.split (Str.regexp "\n") data in
  let clean s = 
    Pcre.replace ~pat:"[ \t]+" ~templ:" "
      (Pcre.replace ~pat:"^ *" (Pcre.replace ~pat:" *$" s))
  in
  List.map 
    (fun l -> 
      match Str.split (Str.regexp "=") l with
      | [k;v] -> clean k, Http_getter_misc.strip_trailing_slash (clean v)
      | _ -> raise (Failure ("Malformed root file: " ^ rootpath)))
    lines
;;

let find_root_for ~include_paths file = 
  let include_paths = "" :: Sys.getcwd () :: include_paths in
   let rec find_path_for file =
      try HExtlib.find_in include_paths file
      with Failure "find_in" -> 
         if Filename.check_suffix file ".ma" then begin
            let mma = Filename.chop_suffix file ".ma" ^ ".mma" in
            HLog.warn ("We look for: " ^ mma);
            let path = find_path_for mma in
	    Filename.chop_suffix path ".mma" ^ ".ma"
         end else begin
            HLog.error ("We are in: " ^ Sys.getcwd ());
            HLog.error ("Unable to find: "^file^"\nPaths explored:");
            List.iter (fun x -> HLog.error (" - "^x)) include_paths;
            raise (NoRootFor file)
         end         
   in
   let path = find_path_for file in   
   let path = absolutize path in
(*     HLog.debug ("file "^file^" resolved as "^path);  *)
   let rootpath, root, buri = 
     try
       let mburi = Helm_registry.get "matita.baseuri" in
       match Str.split (Str.regexp " ") mburi with
       | [root; buri] when HExtlib.is_prefix_of root path -> 
           ":registry:", root, buri
       | _ -> raise (Helm_registry.Key_not_found "matita.baseuri")
     with Helm_registry.Key_not_found "matita.baseuri" -> 
       let rootpath = find_root path in
       let buri = List.assoc "baseuri" (load_root_file rootpath) in
       rootpath, Filename.dirname rootpath, buri
   in
(*     HLog.debug ("file "^file^" rooted by "^rootpath^"");  *)
   let uri = Http_getter_misc.strip_trailing_slash buri in
   if String.length uri < 5 || String.sub uri 0 5 <> "cic:/" then
     HLog.error (rootpath ^ " sets an incorrect baseuri: " ^ buri);
   ensure_trailing_slash root, remove_trailing_slash uri, path
 
;;

let mk_baseuri root extra =
  let chop name = 
    assert(Filename.check_suffix name ".ma" ||
      Filename.check_suffix name ".mma");
    try Filename.chop_extension name
    with Invalid_argument "Filename.chop_extension" -> name
  in
   remove_trailing_slash (HExtlib.normalize_path (root ^ "/" ^ chop extra))
;;

let baseuri_of_script ~include_paths file = 
  let root, buri, path = find_root_for ~include_paths file in
  let path = HExtlib.normalize_path path in
  let root = HExtlib.normalize_path root in
  let lpath = Str.split (Str.regexp "/") path in
  let lroot = Str.split (Str.regexp "/") root in
  let rec substract l1 l2 =
    match l1, l2 with
    | h1::tl1,h2::tl2 when h1 = h2 -> substract tl1 tl2
    | l,[] -> l
    | _ -> raise (NoRootFor (file ^" "^path^" "^root))
  in
  let extra_buri = substract lpath lroot in
  let extra = String.concat "/" extra_buri in
   root,
   mk_baseuri buri extra,
   path,
   extra
;;

let find_roots_in_dir dir =
  HExtlib.find ~test:(fun f ->
    Filename.basename f = "root" &&
    try (Unix.stat f).Unix.st_kind = Unix.S_REG 
    with Unix.Unix_error _ -> false)
    dir
;;

(* make *)
let load_deps_file f = 
  let deps = ref [] in
  let ic = open_in f in
  try
    while true do
      begin
        let l = input_line ic in
        match Str.split (Str.regexp " ") l with
        | [] -> 
            HLog.error ("Malformed deps file: " ^ f); 
            raise (Failure ("Malformed deps file: " ^ f)) 
        | he::tl -> deps := (he,tl) :: !deps
      end
    done; !deps
    with End_of_file -> !deps
;;

type options = (string * string) list

module type Format =
  sig
    type source_object
    type target_object
    val load_deps_file: string -> (source_object * source_object list) list
    val string_of_source_object: source_object -> string
    val string_of_target_object: target_object -> string
    val build: options -> source_object -> bool
    val root_and_target_of: 
          options -> source_object -> 
	   (* root, relative source, writeable target, read only target *)
	   string option * source_object * target_object * target_object
    val mtime_of_source_object: source_object -> float option
    val mtime_of_target_object: target_object -> float option
    val is_readonly_buri_of: options -> source_object -> bool
  end

module Make = functor (F:Format) -> struct

  type status = Done of bool
              | Ready of bool

  let say s = if !debug > 0 then prerr_endline ("make: "^s);; 

  let unopt_or_call x f y = match x with Some _ -> x | None -> f y;;

  let fst4 = function (x,_,_,_) -> x;;

  let modified_before_s_t (_,cs, ct, _, _) a b = 
   
    if !debug > 1 then time_stamp ("L s_t: a " ^ F.string_of_source_object a);
    if !debug > 1 then time_stamp ("L s_t: b " ^ F.string_of_target_object b);
    
    let a = try Hashtbl.find cs a with Not_found -> assert false in
    let b = 
      try
        match Hashtbl.find ct b with
        | Some _ as x -> x
        | None ->
           match F.mtime_of_target_object b with
           | Some t as x -> 
               Hashtbl.remove ct b;
               Hashtbl.add ct b x; x
           | x -> x
      with Not_found -> assert false
    in
    let r = match a, b with 
       | Some a, Some b -> a <= b
       | _ -> false
    in

    if !debug > 1 then time_stamp ("L s_t: " ^ string_of_bool r);

    r

  let modified_before_t_t (_,_,ct, _, _) a b =

    if !debug > 1 then time_stamp ("L t_t: a " ^ F.string_of_target_object a);
    if !debug > 1 then time_stamp ("L t_t: b " ^ F.string_of_target_object b);
    
    let a = 
      try
        match Hashtbl.find ct a with
        | Some _ as x -> x
        | None ->
	   match F.mtime_of_target_object a with
           | Some t as x -> 
  	       Hashtbl.remove ct a;
               Hashtbl.add ct a x; x
           | x -> x
      with Not_found -> assert false
    in
    let b = 
      try
        match Hashtbl.find ct b with
        | Some _ as x -> x
        | None ->
           match F.mtime_of_target_object b with
           | Some t as x -> 
	       Hashtbl.remove ct b;
               Hashtbl.add ct b x; x
           | x -> x
      with Not_found -> assert false
    in
    let r = match a, b with
       | Some a, Some b ->

       if !debug > 1 then time_stamp ("tt: a " ^ string_of_float a);
       if !debug > 1 then time_stamp ("tt: b " ^ string_of_float b);

          a <= b
       | _ -> false
    in

    if !debug > 1 then time_stamp ("L t_t: " ^ string_of_bool r);

    r

  let rec purge_unwanted_roots wanted deps =
    let roots, rest = 
       List.partition 
         (fun (t,_,d,_,_) ->
           not (List.exists (fun (_,_,d1,_,_) -> List.mem t d1) deps))
         deps
    in
    let newroots = List.filter (fun (t,_,_,_,_) -> List.mem t wanted) roots in
    if newroots = roots then
      deps
    else
      purge_unwanted_roots wanted (newroots @ rest)
  ;;

  let is_not_ro (opts,_,_,_,_) (f,_,_,r,_) =
    match r with
    | Some root -> not (F.is_readonly_buri_of opts f)
    | None -> assert false
  ;;

(* FG: new sorting algorithm ************************************************)

  let rec make_aux root opts ok deps =
    List.fold_left (make_one root opts) ok deps
     
  and make_one root opts ok what =
    let lo, _, ct, cc, cd = opts in
    let t, path, deps, froot, tgt = what in
    let str = F.string_of_source_object t in
    let map (okd, okt) d =
       let (_, _, _, _, tgtd) as whatd = (Hashtbl.find cd d) in
       let r = make_one root opts okd whatd in 
       r, okt && modified_before_t_t opts tgtd tgt
    in
    time_stamp ("L : processing " ^ str);
    try 
       let r = Hashtbl.find cc t in
       time_stamp ("L : " ^ string_of_bool r ^ " " ^ str);
       ok && r
(* say "already built" *)
    with Not_found ->
       let okd, okt = List.fold_left map (true, modified_before_s_t opts t tgt) deps in       
       let res = 
          if okd then 
	  if okt then true else
          let build path = match froot with
             | Some froot when froot = root -> 
	        if is_not_ro opts what then F.build lo path else
	        (HLog.error ("Read only baseuri for: " ^ str ^
                   ", I won't compile it even if it is out of date"); 
	        false)
	     | Some froot -> make froot [path]
             | None -> HLog.error ("No root for: " ^ str); false
          in
          Hashtbl.remove ct tgt;
          Hashtbl.add ct tgt None;
          time_stamp ("L : BUILDING " ^ str);
	  let res = build path in
	  time_stamp ("L : DONE     " ^ str); res
          else false
       in
       time_stamp ("L : " ^ string_of_bool res ^ " " ^ str);
       Hashtbl.add cc t res; ok && res

(****************************************************************************)

  and make root targets = 
    time_stamp "L : ENTERING";
    HLog.debug ("Entering directory '"^root^"'");
    let old_root = Sys.getcwd () in
    Sys.chdir root;
    let deps = F.load_deps_file (root^"/depends") in
    let local_options = load_root_file (root^"/root") in
    let baseuri = List.assoc "baseuri" local_options in
    print_endline ("Entering HELM directory: " ^ baseuri); flush stdout;    
    let caches,cachet,cachec,cached = 
       Hashtbl.create 73, Hashtbl.create 73, Hashtbl.create 73, Hashtbl.create 73
    in
    (* deps are enriched with these informations to sped up things later *)
    let deps = 
      List.map 
        (fun (file,d) -> 
          let r,path,wtgt,rotgt = F.root_and_target_of local_options file in
          Hashtbl.add caches file (F.mtime_of_source_object file);
	  (* if a read only target exists, we use that one, otherwise
	     we use the writeable one that may be compiled *)
	  let _,_,_,_, tgt as tuple = 
	    match F.mtime_of_target_object rotgt with
	    | Some _ as mtime ->
               Hashtbl.add cachet rotgt mtime; 
	       (file, path, d, r, rotgt)
	    | None -> 
               Hashtbl.add cachet wtgt (F.mtime_of_target_object wtgt); 
	       (file, path, d, r, wtgt)
	  in
          Hashtbl.add cached file tuple;
          tuple
	)
        deps
    in
    let opts = local_options, caches, cachet, cachec, cached in
    let ok =
      if targets = [] then 
        make_aux root opts true deps
      else
        make_aux root opts true (purge_unwanted_roots targets deps)
    in
    print_endline ("Leaving HELM directory: " ^ baseuri); flush stdout;
    HLog.debug ("Leaving directory '"^root^"'");
    Sys.chdir old_root;
    time_stamp "L : LEAVING";
    ok
  ;;

end
  
let write_deps_file where deps = match where with 
   | Some root ->
      let oc = open_out (root ^ "/depends") in
      let map (t, d) = output_string oc (t^" "^String.concat " " d^"\n") in
      List.iter map deps; close_out oc;
      HLog.message ("Generated: " ^ root ^ "/depends")
   | None -> 
      print_endline (String.concat " " (List.flatten (List.map snd deps)))
      
(* FG ***********************************************************************)

(* scheme uri part as defined in URI Generic Syntax (RFC 3986) *)
let uri_scheme_rex = Pcre.regexp "^[[:alpha:]][[:alnum:]\-+.]*:"

let is_uri str =
   Pcre.pmatch ~rex:uri_scheme_rex str
