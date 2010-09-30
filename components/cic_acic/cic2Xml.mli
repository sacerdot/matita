(* Copyright (C) 2000, HELM Team.
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

exception NotImplemented

val print_term :
  ?ids_to_inner_sorts: (string, Cic2acic.sort_kind) Hashtbl.t ->
  Cic.annterm ->
    Xml.token Stream.t

val print_object :
  UriManager.uri ->
  ?ids_to_inner_sorts: (string, Cic2acic.sort_kind) Hashtbl.t ->
  ?generate_attributes:bool ->
  ask_dtd_to_the_getter:bool ->
  Cic.annobj ->
    Xml.token Stream.t * Xml.token Stream.t option

val print_inner_types :
  UriManager.uri ->
  ids_to_inner_sorts: (string, Cic2acic.sort_kind) Hashtbl.t ->
  ids_to_inner_types: (string, Cic2acic.anntypes) Hashtbl.t ->
  ask_dtd_to_the_getter:bool ->
    Xml.token Stream.t

