(* Copyright (C) 2004-2005, HELM Team.
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

  (** for debugging only *)
val all_disambiguation_passes: bool ref

  (** singleton instance of the gui *)
val instance: unit -> MatitaGuiTypes.gui

  (** {2 Disambiguation callbacks}
  * Use singleton gui instance. *)

  (** @param selection_mode selection mode in uri list, default to `MULTIPLE
    * @param title window title, defaults to ""
    * @param msg message for the user, defaults to ""
    * @param nonvars_button enable button to exclude vars?, defaults to false
    * @raise MatitaTypes.Cancel *)
val interactive_uri_choice:
  ?selection_mode:([`SINGLE|`MULTIPLE]) -> ?title:string ->
  ?msg:string -> ?nonvars_button:bool -> 
  ?hide_uri_entry:bool -> ?hide_try:bool -> ?ok_label:string ->
  ?ok_action:[`AUTO|`SELECT] ->
  ?copy_cb:(string -> unit) -> unit ->
  id:'a -> NReference.reference list -> NReference.reference list

  (** @raise MatitaTypes.Cancel *)
val interactive_interp_choice:
  unit ->
    DisambiguateTypes.interactive_interpretation_choice_type

