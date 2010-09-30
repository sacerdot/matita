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

  (** {2 Persistant state handling} *)

type pretty_printer_id

val add_pretty_printer:
  CicNotationPt.term ->             (* level 2 pattern *)
  CicNotationParser.checked_l1_pattern ->
    pretty_printer_id

exception Pretty_printer_not_found

  (** @raise Pretty_printer_not_found *)
val remove_pretty_printer: pretty_printer_id -> unit

  (** {2 content -> pres} *)

val pp_ast: CicNotationPt.term -> CicNotationPt.term

  (** {2 pres -> content} *)

  (** fills a term pattern instantiating variable magics *)
val instantiate_level2:
  CicNotationEnv.t -> CicNotationPt.term ->
    CicNotationPt.term

val push: unit -> unit
val pop: unit -> unit
