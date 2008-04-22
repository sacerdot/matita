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

(** {2 Constructors} *)

  (** meta constructor *)
type 'widget constructor =
  ?hadjustment:GData.adjustment ->
  ?vadjustment:GData.adjustment ->
  ?font_size:int ->
  ?log_verbosity:int ->
  ?width:int ->
  ?height:int ->
  ?packing:(GObj.widget -> unit) ->
  ?show:bool ->
  unit ->
    'widget

val clickableMathView:  MatitaGuiTypes.clickableMathView constructor

val cicMathView:        MatitaGuiTypes.cicMathView constructor

val sequentsViewer:
  notebook:GPack.notebook ->
  cicMathView:MatitaGuiTypes.cicMathView ->
  unit ->
    MatitaGuiTypes.sequentsViewer

val cicBrowser: unit -> MatitaGuiTypes.cicBrowser

(** {2 MathView wide functions} *)
(* TODO ZACK consider exporting here a single function which return a list of
 * MatitaGuiTypes.clickableMathView and act on them externally ... *)

val increase_font_size:   unit -> unit
val decrease_font_size:   unit -> unit
val reset_font_size:      unit -> unit

val refresh_all_browsers: unit -> unit  (** act on all cicBrowsers *)
val update_font_sizes:    unit -> unit

  (** {3 Clipboard & Selection handling} *)

val has_selection: unit -> bool

  (** fills the clipboard with the current selection
   * @raise Failure "no selection" *)
val copy_selection: unit -> unit
val has_clipboard: unit -> bool (** clipboard is not empty *)
val empty_clipboard: unit -> unit (** empty the clipboard *)

  (** @raise Failure "empty clipboard" *)
val paste_clipboard: MatitaGuiTypes.paste_kind -> string

(** {2 Singleton instances} *)

val cicMathView_instance: unit -> MatitaGuiTypes.cicMathView
val sequentsViewer_instance:  unit -> MatitaGuiTypes.sequentsViewer

val mathViewer:               unit -> MatitaTypes.mathViewer

(** {2 Initialization} *)

val set_gui: MatitaGuiTypes.gui -> unit

