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

(* $Id$ *)

type thingsToInitilaize = 
  ConfigurationFile | Db | Environment | Getter | CmdLine | Registry
  
exception FailedToInitialize of thingsToInitilaize

let wants s l = 
  List.iter (
    fun item -> 
      if not (List.exists (fun x -> x = item) l) then
        raise (FailedToInitialize item)) 
  s

let already_configured s l =
  List.for_all (fun item -> List.exists (fun x -> x = item) l) s
  
let conffile = ref BuildTimeConf.matita_conf

let registry_defaults = [
  "matita.debug",                "false";
  "matita.external_editor",      "gvim -f -c 'go %p' %f";
  "matita.profile",              "true";
  "matita.system",               "false";
  "matita.verbose",              "false";
  "matita.paste_unicode_as_tex", "false";
  "matita.noinnertypes",         "false";
  "matita.do_heavy_checks",      "true";
  "matita.moo",                  "true";
  "matita.extract",              "false";
]

let set_registry_values =
  List.iter 
    (fun key, value -> 
       if not (Helm_registry.has key) then Helm_registry.set ~key ~value)

let fill_registry init_status =
  if not (already_configured [ Registry ] init_status) then begin
    set_registry_values registry_defaults;
    Registry :: init_status
  end else
    init_status

let load_configuration init_status =
  if not (already_configured [ConfigurationFile] init_status) then
    begin
      Helm_registry.load_from !conffile;
      if not (Helm_registry.has "user.name") then begin
        let login = (Unix.getpwuid (Unix.getuid ())).Unix.pw_name in
        Helm_registry.set "user.name" login
      end;
      let home = Helm_registry.get_string "matita.basedir" in
      let user_conf_file = home ^ "/matita.conf.xml" in
      if HExtlib.is_regular user_conf_file then
        begin
          HLog.message ("Loading additional conf file from " ^ user_conf_file);
          try
            Helm_registry.load_from user_conf_file
          with exn -> 
            HLog.error
              ("While loading conf file: " ^ snd (MatitaExcPp.to_string exn))
        end;
      ConfigurationFile::init_status 
    end
  else
    init_status

let initialize_db init_status = 
  wants [ ConfigurationFile; CmdLine ] init_status;
  if not (already_configured [ Db ] init_status) then
    begin
      if not (Helm_registry.get_bool "matita.system") then
        MetadataTypes.ownerize_tables (Helm_registry.get "matita.owner");
      LibraryDb.create_owner_environment ();
      Db::init_status
    end
  else
    init_status

let initialize_environment init_status = 
  wants [CmdLine] init_status;
  if not (already_configured [Getter;Environment] init_status) then
    begin
      Http_getter.init ();
      if Helm_registry.get_bool "matita.system" then
        Http_getter_storage.activate_system_mode ();
      CicEnvironment.set_trust (* environment trust *)
        (let trust =
          Helm_registry.get_opt_default Helm_registry.get_bool
            ~default:true "matita.environment_trust" in
         fun _ -> trust);
      Getter::Environment::init_status
    end
  else
    init_status 
  
let status = ref []

let usages = Hashtbl.create 11 (** app name (e.g. "matitac") -> usage string *)
let _ =
  List.iter
    (fun (name, s) -> Hashtbl.replace usages name s)
    [ "matitac", 
        Printf.sprintf "Matita batch compiler v%s
Usage: matitac [ OPTION ... ] FILE
Options:"
          BuildTimeConf.version;
        "matitaprover",
        Printf.sprintf "Matita (TPTP) prover v%s
Usage: matitaprover [ -tptppath ] FILE.p
Options:"
          BuildTimeConf.version;
      "matita",
        Printf.sprintf "Matita interactive theorem prover v%s
Usage: matita [ OPTION ... ] [ FILE ]
Options:"
          BuildTimeConf.version;
      "matitadep",
        Printf.sprintf "Matita depency file generator v%s
Usage: matitadep [ OPTION ... ] 
Options:"
          BuildTimeConf.version;
      "matitaclean",
        Printf.sprintf "MatitaClean v%s
Usage: matitaclean all
       matitaclean ( FILE | URI )
Options:"
          BuildTimeConf.version;
    ]
let default_usage =
  Printf.sprintf 
    "Matita v%s\nUsage: matita [ ARG ]\nOptions:" BuildTimeConf.version

let usage () =
  let basename = Filename.basename Sys.argv.(0) in
  let usage_key =
    try Filename.chop_extension basename with Invalid_argument  _ -> basename
  in
  try Hashtbl.find usages usage_key with Not_found -> default_usage
;;

let dump f =
   let module G = GrafiteAst in
   let module L = LexiconAst in
   let module H = HExtlib in
   Helm_registry.set_bool "matita.moo" false;
   let floc = H.dummy_floc in
   let nl_ast = G.Comment (floc, G.Note (floc, "")) in
   let och = open_out f in
   let atexit () = close_out och in
   let out_comment och s =
      let s = if s <> "" && s.[0] = '*' then "#" ^ s else s in 
      Printf.fprintf och "%s%s%s\n\n" "(*" s "*)"
   in
   let out_line_comment och s =
      let l = 70 - String.length s in
      let s = Printf.sprintf " %s %s" s (String.make l '*') in
      out_comment och s
   in
   let out_preamble och (path, lines) =
      let ich = open_in path in
      let rec print i =
         if i > 0 then 
            let s = input_line ich in
            begin Printf.fprintf och "%s\n" s; print (pred i) end
      in 
      print lines;
      out_line_comment och "This file was automatically generated: do not edit"
   in
   let pp_ast_statement st =
     GrafiteAstPp.pp_statement ~term_pp:CicNotationPp.pp_term
       ~map_unicode_to_tex:(Helm_registry.get_bool
         "matita.paste_unicode_as_tex")
       ~lazy_term_pp:CicNotationPp.pp_term 
       ~obj_pp:(CicNotationPp.pp_obj CicNotationPp.pp_term) st
   in
   let nl () =  output_string och (pp_ast_statement nl_ast) in
   let rt_base_dir = Filename.dirname Sys.argv.(0) in
   let path = Filename.concat rt_base_dir "matita.ma.templ" in
   let lines = 14 in
   out_preamble och (path, lines);
   let grafite_parser_cb fname = 
      let ast = G.Executable 
        (floc, G.Command (floc, G.Include (floc, fname))) in
      output_string och (pp_ast_statement ast); nl (); nl ()
   in
   let matita_engine_cb = function
      | G.Executable (_, G.Macro (_, G.Inline _)) 
      | G.Executable (_, G.Command (_, G.Include _)) -> ()
      | ast                                          ->
         output_string och (pp_ast_statement ast); nl (); nl ()
   in
   let matitac_lib_cb = output_string och in
   GrafiteParser.set_callback grafite_parser_cb;
   MatitaEngine.set_callback matita_engine_cb;
   MatitacLib.set_callback matitac_lib_cb;
   at_exit atexit
;;

let extra_cmdline_specs = ref []
let add_cmdline_spec l = extra_cmdline_specs := l @ !extra_cmdline_specs

let parse_cmdline init_status =
  if not (already_configured [CmdLine] init_status) then begin
    wants [Registry] init_status;
    let includes = ref [] in
    let default_includes = [ 
      BuildTimeConf.stdlib_dir_devel;
      BuildTimeConf.stdlib_dir_installed ; ] 
    in
    let absolutize s =
      if Pcre.pmatch ~pat:"^/" s then s else Sys.getcwd () ^"/"^s
    in
    let args = ref [] in
    let add_l l = fun s -> l := s :: !l in
    let print_version () =
            Printf.printf "%s\n" BuildTimeConf.version;exit 0 in
    let no_innertypes () =
      Helm_registry.set_bool "matita.noinnertypes" true in
    let set_baseuri s =
      match Str.split (Str.regexp "::") s with
      | [path; uri] -> Helm_registry.set "matita.baseuri"
          (HExtlib.normalize_path (absolutize path)^" "^uri)
      | _ -> raise (Failure "bad baseuri, use -b 'path::uri'")
    in
    let arg_spec =
      let std_arg_spec = [
        "-b", Arg.String set_baseuri, "<path::uri> forces the baseuri of path";
        "-I", Arg.String (add_l includes),
          ("<path> Adds path to the list of searched paths for the "
           ^ "include command");
        "-conffile", Arg.Set_string conffile,
          (Printf.sprintf ("<filename> Read configuration from filename"
             ^^ "\n    Default: %s")
            BuildTimeConf.matita_conf);
        "-force",
            Arg.Unit (fun () -> Helm_registry.set_bool "matita.force" true),
            ("Force actions that would not be executed per default");
        "-noprofile", 
          Arg.Unit (fun () -> Helm_registry.set_bool "matita.profile" false),
          "Turns off profiling printings";
        "-noinnertypes", Arg.Unit no_innertypes, 
          "Turns off inner types generation while publishing";
        "-profile-only",
          Arg.String (fun rex -> Helm_registry.set "matita.profile_only" rex),
          "Activates only profiler with label matching the provided regex";
        "-system", Arg.Unit (fun () ->
              Helm_registry.set_bool "matita.system" true),
            ("Act on the system library instead of the user one"
             ^ "\n    WARNING: not for the casual user");
        "-dump", Arg.String dump,
          "<filename> Dump with expanded macros to <filename>";
        "-v", 
          Arg.Unit (fun () -> Helm_registry.set_bool "matita.verbose" true), 
          "Verbose mode";
        "--version", Arg.Unit print_version, "Prints version";
      ] in
      let debug_arg_spec =
        if BuildTimeConf.debug then
          [ "-debug",
            Arg.Unit (fun () -> Helm_registry.set_bool "matita.debug" true),
              ("Do not catch top-level exception "
              ^ "(useful for backtrace inspection)");
	    "-onepass",
	    Arg.Unit (fun () -> GrafiteDisambiguator.only_one_pass := true),
	    "Enable only one disambiguation pass";    
          ]
        else []
      in
      std_arg_spec @ debug_arg_spec @ !extra_cmdline_specs
    in
    let set_list ~key l =
      Helm_registry.set_list Helm_registry.of_string ~key ~value:l
    in
    Arg.parse arg_spec (add_l args) (usage ());
    let includes = 
      List.map (fun x -> HExtlib.normalize_path (absolutize x)) 
       ((List.rev !includes) @ default_includes) 
    in
    set_list ~key:"matita.includes" includes;
    let args = List.rev (List.filter (fun x -> x <> "") !args) in
    set_list ~key:"matita.args" args;
    HExtlib.set_profiling_printings 
      (fun s -> 
        Helm_registry.get_bool "matita.profile" && 
        Pcre.pmatch 
          ~pat:(Helm_registry.get_opt_default 
                  Helm_registry.string ~default:".*" "matita.profile_only") 
          s);
    CmdLine :: init_status
  end else
    init_status

let die_usage () =
  print_endline (usage ());
  exit 1

let conf_components = 
  [ load_configuration; fill_registry; parse_cmdline]

let other_components =
  [ initialize_db; initialize_environment ]

let initialize_all () =
  status := 
    List.fold_left (fun s f -> f s) !status
    (conf_components @ other_components)

let parse_cmdline_and_configuration_file () =
  status := List.fold_left (fun s f -> f s) !status conf_components

let initialize_environment () =
  status := initialize_environment !status

let _ =
  Inversion_principle.init ()
