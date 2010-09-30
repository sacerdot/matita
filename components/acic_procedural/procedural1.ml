(* Copyright (C) 2003-2005, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

module C    = Cic
module A    = Cic2acic
module G    = GrafiteAst

module T    = ProceduralTypes

type status = {
   sorts    : (C.id, A.sort_kind) Hashtbl.t;
   types    : (C.id, A.anntypes) Hashtbl.t;
   params   : G.inline_param list;
   context  : C.context
}

(* interface functions ******************************************************)

let proc_proof st what =
   let dtext = "" in
   [T.Exact (what, dtext)]

let init ~ids_to_inner_sorts ~ids_to_inner_types params context =
   {
      sorts       = ids_to_inner_sorts;
      types       = ids_to_inner_types;
      params      = params;
      context     = context
   }
