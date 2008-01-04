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

val eval_ast :
  ?do_heavy_checks:bool ->
  LexiconEngine.status ->
  GrafiteTypes.status ->
  string * int *
  ((CicNotationPt.term, CicNotationPt.term,
   CicNotationPt.term GrafiteAst.reduction, CicNotationPt.term CicNotationPt.obj, string)
   GrafiteAst.statement) ->
  ((GrafiteTypes.status * LexiconEngine.status) *
   (DisambiguateTypes.domain_item * DisambiguateTypes.codomain_item) option
  ) list


(* heavy checks slow down the compilation process but give you some interesting
 * infos like if the theorem is a duplicate *)

(* should be used only by the compiler since it looses the
   * disambiguation_context (text,prefix_len,_) *)
val eval_from_stream :
  first_statement_only:bool ->
  include_paths:string list ->
  ?prompt:bool ->
  ?do_heavy_checks:bool ->
  ?enforce_no_new_aliases:bool -> (* default true *)
  ?watch_statuses:(LexiconEngine.status -> GrafiteTypes.status -> unit) ->
  LexiconEngine.status ->
  GrafiteTypes.status ->
  Ulexing.lexbuf ->
  (GrafiteTypes.status ->
   (CicNotationPt.term, CicNotationPt.term,
    CicNotationPt.term GrafiteAst.reduction, CicNotationPt.term CicNotationPt.obj, string)
   GrafiteAst.statement -> unit) ->
  ((GrafiteTypes.status * LexiconEngine.status) *
   (DisambiguateTypes.domain_item * DisambiguateTypes.codomain_item) option
  ) list

(* this callback is called on every grafite command *)
val set_callback: (GrafiteParser.ast_statement -> unit) -> unit 
