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

type 'a localized_option =
   LSome of 'a
 | LNone of GrafiteAst.loc

type ast_statement =
  (CicNotationPt.term, CicNotationPt.term,
   CicNotationPt.term GrafiteAst.reduction, 
   CicNotationPt.term CicNotationPt.obj, string)
    GrafiteAst.statement

exception NoInclusionPerformed of string (* full path *)

type 'status statement =
  ?never_include:bool -> 
    (* do not call LexiconEngine to do includes, always raise NoInclusionPerformed *) 
  include_paths:string list ->
  (#LexiconEngine.status as 'status) ->
    'status * ast_statement localized_option

val parse_statement: Ulexing.lexbuf -> #LexiconEngine.status statement  (** @raise End_of_file *)

val statement: unit -> #LexiconEngine.status statement Grammar.Entry.e

(* this callback is called before every grafite statement *)
val set_grafite_callback:
   (ast_statement -> unit) -> unit 

(* this callback is called before every lexicon command *)
val set_lexicon_callback:
   (LexiconAst.command -> unit) -> unit 

val push : unit -> unit
val pop : unit -> unit
