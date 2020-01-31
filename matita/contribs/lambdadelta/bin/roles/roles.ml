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
let help_C = "<dir>  Set this working directory (default: current directory)"
let help_L = " Debug osn lexer"
let help_W = " Run as an LWS application"
let help_X = " Reset all options to defaults"
let help_a = " Add selected names to a role"
let help_m = " Add roles relating matching names"
let help_o = "<version>  Add top objects for this stage"
let help_p = " Print current status on standard output"
let help_r = " Load current status"
let help_s = "<version>  Start a stage with this version"
let help_t = "<pointer>  Toggle the selection of this pointed entry"
let help_w = " Save current status"
let help   = "Usage: roles [ -LWXamprw | -B <url> | -C <dir> | -os <version> | -t <pointer> | <file> ]*"

let add_tops s =
  EE.add_tops (EU.version_of_string s)

let new_stage s =
  EE.new_stage (EU.version_of_string s)

let toggle_entry s =
  EE.toggle_entry (EU.pointer_of_string s)

let process s =
  match Filename.extension s with
  | ".txt" -> EE.read_waiting s
  | x      -> EU.raise_error (ET.EWrongExt x)

let _main = try
  Arg.parse [
    "-B", Arg.String ((:=) EG.base_url), help_B;
    "-C", Arg.String ((:=) EG.wd), help_C;
    "-L", Arg.Set EG.debug_lexer, help_L;
    "-W", Arg.Unit WE.init, help_W;
    "-X", Arg.Unit EG.clear, help_X;
    "-a", Arg.Unit EE.add_role, help_a;
    "-m", Arg.Unit EE.add_matching, help_m;
    "-o", Arg.String add_tops, help_o;
    "-p", Arg.Unit EE.print_status, help_p;
    "-r", Arg.Unit EE.read_status, help_r;
    "-s", Arg.String new_stage, help_s;
    "-t", Arg.String toggle_entry, help_t;
    "-w", Arg.Unit EE.write_status, help_w;
  ] process help
with ET.Error e -> Printf.eprintf "roles: %s\n%!" (EU.string_of_error e)
