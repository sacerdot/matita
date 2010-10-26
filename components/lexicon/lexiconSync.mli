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

val add_aliases_for_objs:
 #LexiconEngine.status as 'status -> NUri.uri list -> 'status

val time_travel: 
  present:#LexiconEngine.status -> past:#LexiconEngine.status -> unit

  (** perform a diff between the aliases contained in two statuses, assuming
    * that the second one can only have more aliases than the first one
    * @return the list of aliases that should be added to aliases of from in
    * order to be equal to aliases of the second argument *)
val alias_diff:
 from:#LexiconEngine.status -> #LexiconEngine.status ->
  (DisambiguateTypes.domain_item * LexiconAst.alias_spec) list

val push: unit -> unit
val pop: unit -> unit
