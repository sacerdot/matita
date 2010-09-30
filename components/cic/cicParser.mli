(* Copyright (C) 2000-2005, HELM Team.
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

  (** raised for exception received by the getter (i.e. embedded in the source
   * XML document). Arguments are values of "helm:exception" and
   * "helm:exception_arg" attributes *)
exception Getter_failure of string * string

  (** generic parser failure *)
exception Parser_failure of string

  (* given the filename of an xml file of a cic object, it returns
   * its internal annotated representation. In the case of constants (whose
   * type is splitted from the body), a second xml file (for the body) must be
   * provided.
   * Both files are assumed to be gzipped. *)
val annobj_of_xml: UriManager.uri -> string -> string option -> Cic.annobj

  (* given the filename of an xml file of a cic object, it returns its internal
   * logical representation. In the case of constants (whose type is splitted
   * from the body), a second xml file (for the body) must be provided.
   * Both files are assumed to be gzipped. *)
val obj_of_xml : UriManager.uri -> string -> string option -> Cic.obj

val impredicative_set : bool ref
