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

val pp_tactic:
  map_unicode_to_tex:bool ->
  term_pp:('term -> string) ->
  lazy_term_pp:('lazy_term -> string) ->
  ('term, 'lazy_term, 'term GrafiteAst.reduction, string)
  GrafiteAst.tactic ->
    string

val pp_tactic_pattern:
  map_unicode_to_tex:bool ->
  term_pp:('term -> string) ->
  lazy_term_pp:('lazy_term -> string) ->
  ('term, 'lazy_term, string) GrafiteAst.pattern ->
    string

val pp_reduction_kind:
  term_pp:('a -> string) ->
  'a GrafiteAst.reduction ->
    string

val pp_command: GrafiteAst.command -> string
val pp_comment:
  map_unicode_to_tex:bool ->
  term_pp:('term -> string) ->
  lazy_term_pp:('lazy_term -> string) ->
  obj_pp:('obj -> string) ->
  ('term, 'lazy_term, 'term GrafiteAst.reduction, 'obj, string)
  GrafiteAst.comment ->
    string

val pp_executable:
  map_unicode_to_tex:bool ->
  term_pp:('term -> string) ->
  lazy_term_pp:('lazy_term -> string) ->
  obj_pp:('obj -> string) ->
  ('term, 'lazy_term, 'term GrafiteAst.reduction, 'obj, string)
  GrafiteAst.code ->
    string

val pp_statement:
  term_pp:('term -> string) ->
  lazy_term_pp:('lazy_term -> string) ->
  obj_pp:('obj -> string) ->
  ('term, 'lazy_term, 'term GrafiteAst.reduction, 'obj, string)
  GrafiteAst.statement ->
  map_unicode_to_tex:bool ->
    string

val pp_punctuation_tactical: GrafiteAst.punctuation_tactical -> string

