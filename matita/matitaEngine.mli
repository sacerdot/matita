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

exception TryingToAdd of string Lazy.t
exception EnrichedWithStatus of exn * GrafiteTypes.status
exception AlreadyLoaded of string Lazy.t
exception FailureCompiling of string * exn
exception CircularDependency of string

val get_ast:
  GrafiteTypes.status -> include_paths:string list -> GrafiteParser.parsable ->
    GrafiteAst.statement

(* heavy checks slow down the compilation process but give you some interesting
 * infos like if the theorem is a duplicate *)
val eval_ast :
  include_paths: string list ->
  ?do_heavy_checks:bool ->
  GrafiteTypes.status ->
  string * int *
  GrafiteAst.statement ->
  (GrafiteTypes.status *
   (DisambiguateTypes.domain_item * GrafiteAst.alias_spec) option) list

val assert_ng : include_paths:string list -> root:string -> string -> bool
