(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department, University of Bologna, Italy.
    ||I||
    ||T||  HELM is free software; you can redistribute it and/or
    ||A||  modify it under the terms of the GNU General Public License
    \   /  version 2 or (at your option) any later version.
     \ /   This software is distributed as is, NO WARRANTY.
      V_______________________________________________________________ *)

module EE = RolesEngine
module EG = RolesGlobal
module ET = RolesTypes
module EU = RolesUtils
module WE = WebEngine

let help_B = "<url>  Set this base url (default: http://helm.cs.unibo.it/lambdadelta/)"
let help_C = "<dir>  Set this relative working directory (default: invocation directory)"
let help_L = " Debug osn lexer"
let help_W = " Run as an LWS application"
let help_X = " Reset all options to defaults"
let help_a = " Add selected names to a role"
let help_d = " Remove selected names from roles"
let help_m = " Add roles relating matching names"
let help_n = "<version>  Start a stage with this version"
let help_p = " Print current status on standard output"
let help_r = " Load current status"
let help_s = "<pointer>  Toggle the selection of this pointed entry"
let help_t = "<version>  Add top objects for this stage"
let help_w = " Save current status"
let help_x = "<pointer>  Toggle the expansion of this pointed entry"
let help   = "Usage: roles [ -LWXadmprw | -B <url> | -C <dir> | -nt <version> | -sx <pointer> | <file> ]*"

let change_cwd s =
  EG.cwd := Filename.concat !EG.cwd s

let add_tops s =
  EE.add_tops (EU.stage_of_string s)

let new_stage s =
  EE.new_stage (EU.stage_of_string s)

let select_entry s =
  EE.select_entry (EU.pointer_of_string s)

let expand_entry s =
  EE.expand_entry (EU.pointer_of_string s)

let process s =
  match Filename.extension s with
  | ".txt" -> EE.read_waiting s
  | x      -> EU.raise_error (ET.EWrongExt x)

let _main = try
  Arg.parse [
    "-B", Arg.String ((:=) EG.base_url), help_B;
    "-C", Arg.String change_cwd, help_C;
    "-L", Arg.Set EG.debug_lexer, help_L;
    "-W", Arg.Unit WE.init, help_W;
    "-X", Arg.Unit EG.clear, help_X;
    "-a", Arg.Unit EE.add_role, help_a;
    "-d", Arg.Unit EE.remove_roles, help_d;
    "-m", Arg.Unit EE.add_matching, help_m;
    "-n", Arg.String new_stage, help_n;
    "-p", Arg.Unit EE.print_status, help_p;
    "-r", Arg.Unit EE.read_status, help_r;
    "-s", Arg.String select_entry, help_s;
    "-t", Arg.String add_tops, help_t;
    "-w", Arg.Unit EE.write_status, help_w;
    "-x", Arg.String expand_entry, help_x;
  ] process help
with ET.Error e -> Printf.eprintf "roles: %s\n%!" (EU.string_of_error e)
