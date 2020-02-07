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

module KP = Printf

module EE = RolesEngine
module EG = RolesGlobal
module ET = RolesTypes
module EU = RolesUtils
module WS = WebLWS

let error = ref ""

let open_out () =
  let author = "λδ development binary: roles manager" in
  let description = "λδ development binary: roles manager" in
  let title = "Roles Manager" in
  let css = Filename.concat !EG.base_url "css/roles.css" in
  let icon = Filename.concat !EG.base_url "images/crux_32.ico" in
  WS.open_out_html author description title css icon

let close_out () =
  WS.close_out_html ()

let string_of_request req arg =
  WS.string_of_request "roles" (["system-"^req, arg], "")

let status_out () =
  let button_specs = [
    "default", "Refresh";
    "save", "Save";
    "add", "Add";
    "match", "Match";
    "remove", "Remove";
  ] in
  let each_button (action, str) =
    let req = string_of_request action "" in 
    KP.printf "<span class=\"button\"><a href=\"%s\">%s</a></span>\n" req str
  in
  let before_roles p count =
    let req = string_of_request "select" p in
    KP.printf "<div class=\"roles-head role-color\">\n";
    KP.printf "<a href=\"%s\">Roles:</a>\n" req;
    KP.printf "<span class=\"count\">%s</span>\n" count
  in
  let each_role p b str =
    let req = string_of_request "select" p in
    let s = if b then " selected" else "" in
    KP.printf "<div class=\"role role-color%s\">" s;
    KP.printf "<a href=\"#%s\">⮞</a> " p;
    KP.printf "<a href=\"%s\">%s</a>" req str;
    KP.printf "</div>\n"
  in
  let before_role () =
    KP.printf "<div class=\"roles\">\n";
  in
  let after_role () =
    KP.printf "</div>\n"
  in
  let after_roles () =
    KP.printf "</div>\n";
    KP.printf "<div class=\"buttons\">\n";
    List.iter each_button button_specs;
    KP.printf "</div>\n"
  in
  let stage s m =
    let msg_m = if m then " (modified)" else "" in
    KP.printf "<div class=\"stage role-color\">";
    KP.printf "Stage: %s%s" s msg_m;
    KP.printf "</div>\n"
  in
  let before_atoms a p count =
    let c, str =
      if a then "object-color", "objects"
      else "name-color", "names"
    in
    let req = string_of_request "select" p in
    KP.printf "<div class=\"atoms-head %s\">\n" c;
    KP.printf "<a href=\"%s\">%s:</a>\n" req str;
    KP.printf "<span class=\"count\">%s</span>\n" count;
    KP.printf "</div>\n";
    KP.printf "<div class=\"atoms\"><table class=\"atoms-table\"><tr>\n"
  in
  let each_atom a p b str =
    let c = if a then "object-color" else "name-color" in
    let s = if b then " selected" else "" in
    let req = string_of_request "select" p in
    KP.printf "<td class=\"atom %s%s\"><a href=\"%s\">%s</a></td>\n" c s req str
  in
  let after_atoms () =
    KP.printf "</tr></table></div>\n"
  in
  KP.printf "<div class=\"head\">Role Manager</div>\n";
  EE.visit_status
    before_roles each_role before_role after_role after_roles stage
    (before_atoms true) (each_atom true) after_atoms
    (before_atoms false) (each_atom false) after_atoms;
  if !error <> "" then
    KP.printf "<div class=\"error error-color\">Error: %s</div>\n" !error

let handler opt arg () =
  begin try match opt with
  | "system-default" -> ()
  | "system-add"     -> EE.add_role ()
  | "system-remove"  -> ()
  | "system-match"   -> EE.add_matching ()
  | "system-select"  -> EE.select_entry (EU.pointer_of_string arg)
  | "system-save"    -> EE.write_status ()
  | _                -> EU.raise_error (ET.EWrongRequest (opt, arg))
  with
  | ET.Error e -> error := EU.string_of_error e
  | e          -> error := Printexc.to_string e 
  end;
  open_out ();
  status_out ();
  close_out ();
  error := ""

let init () =
  WS.loop_in ignore handler ignore ()
