(* Copyright (C) 2004, HELM Team.
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

let debug = true;;
let version = Option.value (Option.map Build_info.V1.Version.to_string (Build_info.V1.version())) ~default:"???"(* "%%PKG_MAINTAINER%%" *);;
let undo_history_size = 10;;
let console_history_size = 100;;
let browser_history_size = 100;;
let base_uri = "cic:/matita";;
let phrase_sep = ".";;
let blank_uri = "about:blank";;
let current_proof_uri = "about:current_proof";;
let default_font_size = 10;;
let script_font = "Monospace";;

  (** may be overridden with MATITA_RT_BASE_DIR environment variable, useful for
   * binary distribution installed in user home directories *)
let runtime_base_dir =
  try
    Sys.getenv "MATITA_RT_BASE_DIR"
  with Not_found ->
   match Mysites.Sites.myshare with
      [rt] -> rt (*It was: "/home/claudio/ricerca/matita5/helm/matita/matita"*)
    | _ -> assert false

let images_dir = runtime_base_dir ^ "/icons"
let gtkrc_file = runtime_base_dir ^ "/matita.gtkrc"
let lang_file  = runtime_base_dir ^ "/matita.lang"
let script_template  = runtime_base_dir ^ "/matita.ma.templ"
let core_notation_script = runtime_base_dir ^ "/core_notation.moo"
let matita_conf  = runtime_base_dir ^ "/matita.conf.xml"
let closed_xml = runtime_base_dir ^ "/closed.xml"
let gtkmathview_conf = runtime_base_dir ^ "/gtkmathview.matita.conf.xml"
let new_stdlib_dir_devel = runtime_base_dir ^ "/lib"
(* CSC: no installed standard library
let new_stdlib_dir_installed = runtime_base_dir ^ "/ma/new-standard-library" *)
let help_dir = runtime_base_dir ^ "/help"

