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

(* $Id$ *)

let close_coercion_graph_ref = ref
 (fun _ _ _ _ _ -> [] : 
   CoercDb.coerc_carr -> CoercDb.coerc_carr -> UriManager.uri -> int ->
   string (* baseuri *) ->
     (CoercDb.coerc_carr * CoercDb.coerc_carr * UriManager.uri * int * Cic.obj *
     int * int) list)
;;

let set_close_coercion_graph f = close_coercion_graph_ref := f;;

let close_coercion_graph c1 c2 u sat s = 
  !close_coercion_graph_ref c1 c2 u sat s
;;
