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

class type console =
object
  method message: string -> unit
  method error: string -> unit
  method warning: string -> unit
  method debug: string -> unit
  method clear: unit -> unit

  method log_callback: HLog.log_callback
end

class type browserWin =
object
  inherit MatitaGeneratedGui.browserWin
  method browserUri: GEdit.combo_box_entry
end

class type gui =
object
  method setQuitCallback    : (unit -> unit) -> unit

    (** {2 Access to singleton instances of lower-level GTK widgets} *)

  method fileSel :      MatitaGeneratedGui.fileSelectionWin
  method main :         MatitaGeneratedGui.mainWin
  method findRepl :     MatitaGeneratedGui.findReplWin
  method develList:     MatitaGeneratedGui.develListWin
  method newDevel:      MatitaGeneratedGui.newDevelWin
(*   method toolbar :      MatitaGeneratedGui.toolBarWin *)

  method console:       console
  method sourceView:    GSourceView.source_view

    (** {2 Dialogs instantiation}
     * methods below create a new window on each invocation. You should
     * remember to destroy windows after use *)

  method newBrowserWin:         unit -> browserWin
  method newUriDialog:          unit -> MatitaGeneratedGui.uriChoiceDialog
  method newConfirmationDialog: unit -> MatitaGeneratedGui.confirmationDialog
  method newEmptyDialog:        unit -> MatitaGeneratedGui.emptyDialog

    (** {2 Selections / clipboards handling} *)

  method canCopy:         bool
  method canCut:          bool
  method canDelete:       bool
  method canPaste:        bool
  method canPastePattern: bool

  method markupSelected:  bool

  method copy:         unit -> unit
  method cut:          unit -> unit
  method delete:       unit -> unit
  method paste:        unit -> unit
  method pastePattern: unit -> unit

    (** {2 Utility methods} *)

    (** ask the used to choose a file with the file chooser
    * @param ok_not_exists if set to true returns also non existent files
    * (useful for save). Defaults to false *)
  method chooseFile: ?ok_not_exists:bool -> unit -> string option
  method createDevelopment: containing:string option -> unit

    (** prompt the user for a (multiline) text entry *)
  method askText: ?title:string -> ?msg:string -> unit -> string option

  method loadScript: string -> unit
  method setStar: string -> bool -> unit

    (** {3 Fonts} *)
  method increaseFontSize: unit -> unit
  method decreaseFontSize: unit -> unit
  method resetFontSize: unit -> unit
end

type paste_kind = [ `Term | `Pattern ]

  (** multi selection gtkMathView which handle mactions and hyperlinks. Mactions
  * are handled internally. Hyperlinks are handled by calling an user provided
  * callback *)
class type clickableMathView =
object
  inherit GMathViewAux.multi_selection_math_view

    (** set hyperlink callback. None disable hyperlink handling *)
  method set_href_callback: (string -> unit) option -> unit
  
  method has_selection: bool

    (** @raise Failure "no selection" *)
  method strings_of_selection: (paste_kind * string) list

  method update_font_size: unit
end

class type cicMathView =
object
  inherit clickableMathView

    (** load a sequent and render it into parent widget *)
  method load_sequent: Cic.metasenv -> int -> unit

  method load_object: Cic.obj -> unit
end

class type sequentsViewer =
object
  method reset: unit
  method load_logo: unit
  method load_logo_with_qed: unit
  method load_sequents: GrafiteTypes.incomplete_proof -> unit
  method goto_sequent: int -> unit  (* to be called _after_ load_sequents *)

  method cicMathView: cicMathView
end

class type cicBrowser =
object
  method load: MatitaTypes.mathViewer_entry -> unit
  (* method loadList: string list -> MatitaTypes.mathViewer_entry -> unit *)
  method loadInput: string -> unit
  method mathView: clickableMathView
end

