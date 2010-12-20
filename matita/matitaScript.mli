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

exception NoUnfinishedProof
exception ActionCancelled of string

class type script =
object

  method locked_mark : Gtk.text_mark
  method locked_tag : GText.tag
  method error_tag : GText.tag

    (** @return current status *)
  method grafite_status: GrafiteTypes.status
    
  (** {2 Observers} *)

  method addObserver : (GrafiteTypes.status -> unit) -> unit

  (** {2 Unicode handling} *)
  method nextSimilarSymbol: unit

  (** {2 Undo/redo} *)

  method safe_undo: unit
  method safe_redo: unit

  (** {2 History} *)

  method advance : ?statement:string -> unit -> unit
  method retract : unit -> unit
  method goto: [`Top | `Bottom | `Cursor] -> unit -> unit
  method reset: unit -> unit
  method template: unit -> unit

    (** {2 Selections / clipboards handling} *)

  method markupSelected: bool
  method canCopy: bool
  method canCut: bool
  method canDelete: bool
  (*CSC: WRONG CODE: we should look in the clipboard instead! *)
  method canPaste: bool
  method canPastePattern: bool

  method copy:         unit -> unit
  method cut:          unit -> unit
  method delete:       unit -> unit
  method paste:        unit -> unit
  method pastePattern: unit -> unit

  (** {2 Load/save} *)
  
  method has_name: bool
  (* alwais return a name, use has_name to check if it is the default one *)
  method filename: string 
  method buri_of_current_file: string 
  method include_paths: string list
  method assignFileName : string option -> unit (* to the current active file *)
  method loadFromFile : string -> unit
  method loadFromString : string -> unit
  method saveToFile : unit -> unit

  (** {2 Current proof} (if any) *)

  method stack: Continuationals.Stack.t       (** @raise Statement_error *)

  method setGoal: int option -> unit
  method goal: int option

  (** end of script, true if the whole script has been executed *)
  method eos: bool
  method bos: bool

  (** misc *)
  method clean_dirty_lock: unit
  method set_star: bool -> unit
  method source_view: GSourceView2.source_view
  
  (* debug *)
  method dump : unit -> unit
  method expandAllVirtuals : unit 

end

val script: 
  urichooser: (GSourceView2.source_view -> NReference.reference list -> NReference.reference list) -> 
  ask_confirmation: 
    (title:string -> message:string -> [`YES | `NO | `CANCEL]) -> 
  unit -> 
    script

(* each time script above is called an internal ref is set, instance will return
 * the value of this ref *)
(* TODO Zack: orrible solution until we found a better one for having a single
 * access point for the script *)
val current: unit -> script

