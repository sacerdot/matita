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
  let author = "λδ development binary: role manager" in
  let description = "λδ development binary: role manager" in
  let title = "Role Manager" in
  let icon = Filename.concat !EG.base_url "images/crux_32.ico" in
  let css = Filename.concat !EG.base_url "css/roles.css" in
  let js = Filename.concat !EG.base_url "js/roles.js" in
  WS.open_out_html author description title icon css js

let close_out () =
  WS.close_out_html ()

let string_of_request req arg =
  WS.string_of_request "roles" (["system-"^req, arg], "")

let status_out () =
  let filter p =
    let req = string_of_request "select" p in
    let ph = "Filter..." in
    KP.printf "<input class=\"filter\" type=\"text\" autocomplete=\"on\" \
      placeholder=%S oninput=\"filter('%s','%s');\" id=\"f.%s\"\n/>" ph req p p
  in
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
    KP.printf "<a id=\"s.%s\" href=\"%s\">Roles:</a>\n" p req;
    KP.printf "<span class=\"count\">%s</span>\n" count;
    filter p
  in
  let each_role n p b k o str =
    let req_x = string_of_request "expand" p in
    let req_s = string_of_request "select" p in
    let s = if b then " selected" else "" in
    KP.printf "<div class=\"role role-color%s\" name=%S key=%S ord=%S>" s n k o;
    KP.printf "<a href=\"%s\">⮞</a> " req_x;
    KP.printf "<a href=\"%s\">%s</a>" req_s str
  in
  let before_role x n o =
    let msg_n = if n then " (added)" else "" in
    let msg_o = if o then " (removed)" else "" in
    KP.printf "%s%s</div>\n" msg_n msg_o;
    if x then KP.printf "<div class=\"roles\">\n"
  in
  let after_role x =
    if x then KP.printf "</div>\n"
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
    KP.printf "<a id=\"s.%s\" href=\"%s\">%s:</a>\n" p req str;
    KP.printf "<span class=\"count\">%s</span>\n" count;
    filter p;
    KP.printf "</div>\n";
    KP.printf "<div class=\"atoms\"><table class=\"atoms-table\"><tr>\n"
  in
  let each_atom a n p b k o str =
    let c = if a then "object-color" else "name-color" in
    let s = if b then " selected" else "" in
    let req = string_of_request "select" p in
    KP.printf "<td class=\"atom %s%s\" name=%S key=%S ord=%S>\
      <a href=\"%s\">%s</a></td>\n" c s n k o req str
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
  | "system-remove"  -> EE.remove_roles ()
  | "system-match"   -> EE.add_matching ()
  | "system-select"  -> EE.select_entry (EU.pointer_of_string arg)
  | "system-save"    -> EE.write_status ()
  | "system-expand"  -> EE.expand_entry (EU.pointer_of_string arg)
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
