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
  ConfigurationFile | Db | Environment | Getter | Makelib | CmdLine | Registry
  
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
  "matita.preserve",             "false";
  "matita.profile",              "true";
  "matita.system",               "false";
  "matita.verbosity",            "1";
  "matita.bench",                "false";
  "matita.paste_unicode_as_tex", "false"
    (** verbosity level: 1 is the default, 0 is intuitively "quiet", > 1 is
     * intuitively verbose *)
]

let set_registry_values =
  List.iter (fun key, value -> Helm_registry.set ~key ~value)

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

let initialize_makelib init_status = 
  wants [ConfigurationFile] init_status;
  if not (already_configured [Makelib] init_status) then
    begin
      MatitamakeLib.initialize (); 
      Makelib::init_status
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
        Printf.sprintf "MatitaC v%s
Usage: matitac [ OPTION ... ] FILE
Options:"
          BuildTimeConf.version;
      "gragrep",
        Printf.sprintf "Grafite Grep v%s
Usage: gragrep [ -r ] PATH
Options:"
          BuildTimeConf.version;
      "matitaprover",
        Printf.sprintf "Matita's prover v%s
Usage: matitaprover [ -tptppath ] FILE.p
Options:"
          BuildTimeConf.version;
      "matita",
        Printf.sprintf "Matita v%s
Usage: matita [ OPTION ... ] [ FILE ... ]
Options:"
          BuildTimeConf.version;
      "cicbrowser",
        Printf.sprintf
          "CIC Browser v%s
Usage: cicbrowser [ URL | WHELP QUERY ]
Options:"
          BuildTimeConf.version;
      "matitadep",
        Printf.sprintf "MatitaDep v%s
Usage: matitadep [ OPTION ... ] FILE ...
Options:"
          BuildTimeConf.version;
      "matitaclean",
        Printf.sprintf "MatitaClean v%s
Usage: matitaclean all
       matitaclean [ (FILE | URI) ... ]
Options:"
          BuildTimeConf.version;
      "matitamake",
        Printf.sprintf "MatitaMake v%s
Usage: matitamake [ OPTION ... ] (init | clean | list | destroy | build)
  init
    Parameters: name (the name of the development, required)
                root (the directory in which the delopment is rooted, 
                      optional, default is current working directory)
    Description: tells matitamake that a new development radicated 
      in the current working directory should be handled.
  clean
    Parameters: name (the name of the development to destroy, optional)
      If omitted the development that holds the current working 
      directory is used (if any).
    Description: clean the develpoment.
  list
    Parameters: 
    Description: lists the known developments and their roots.
  destroy
    Parameters: name (the name of the development to destroy, required)
    Description: deletes a development (only from matitamake metadat, no
      .ma files will be deleted).
  build
    Parameters: name (the name of the development to build, required)
    Description: completely builds the develpoment.
  publish
    Parameters: name (the name of the development to publish, required)
    Description: cleans the development in the user space, rebuilds it
      in the system space ('ro' repositories, that for this operation 
      becames writable). 
Notes:
  If target is omitted an 'all' will be used as the default.
  With -build you can build a development wherever it is.
  If you specify a target it implicitly refers to the development that
  holds the current working directory (if any).
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

let extra_cmdline_specs = ref []
let add_cmdline_spec l = extra_cmdline_specs := l @ !extra_cmdline_specs

let parse_cmdline init_status =
  if not (already_configured [CmdLine] init_status) then begin
    wants [Registry] init_status;
    let includes = ref [] in
    let default_includes = [ 
      ".";
      BuildTimeConf.stdlib_dir_devel;
      BuildTimeConf.stdlib_dir_installed ; ] 
    in
    let absolutize s =
      if Pcre.pmatch ~pat:"^/" s then s else Sys.getcwd() ^"/"^s
    in
    let args = ref [] in
    let add_l l = fun s -> l := s :: !l in
    let reduce_verbosity () =
      Helm_registry.set_int "matita.verbosity"
        (Helm_registry.get_int "matita.verbosity" - 1) in
    let print_version () =
            Printf.printf "%s\n" BuildTimeConf.version;exit 0 in
    let increase_verbosity () =
      Helm_registry.set_int "matita.verbosity"
        (Helm_registry.get_int "matita.verbosity" + 1) in
    let no_innertypes () =
      Helm_registry.set_bool "matita.noinnertypes" false in
    let arg_spec =
      let std_arg_spec = [
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
        "-bench", 
          Arg.Unit (fun () -> Helm_registry.set_bool "matita.bench" true),
          "Turns on parsable output on stdout, that is timings for matitac...";
        "-preserve",
          Arg.Unit (fun () -> Helm_registry.set_bool "matita.preserve" true),
          "Turns off automatic baseuri cleaning";
        "-q", Arg.Unit reduce_verbosity, "Reduce verbosity";
        "-system", Arg.Unit (fun () ->
              Helm_registry.set_bool "matita.system" true),
            ("Act on the system library instead of the user one"
             ^ "\n    WARNING: not for the casual user");
        "-v", Arg.Unit increase_verbosity, "Increase verbosity";
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
      List.map absolutize ((List.rev !includes) @ default_includes) in
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
  [ initialize_makelib; initialize_db; initialize_environment ]

let initialize_all () =
  status := 
    List.fold_left (fun s f -> f s) !status
    (conf_components @ other_components)
(*     initialize_notation 
      (initialize_environment 
        (initialize_db 
          (initialize_makelib
            (load_configuration
              (parse_cmdline !status))))) *)

let parse_cmdline_and_configuration_file () =
  status := List.fold_left (fun s f -> f s) !status conf_components

let initialize_environment () =
  status := initialize_environment !status

let _ =
  Inversion_principle.init ()
