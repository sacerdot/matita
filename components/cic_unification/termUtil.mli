(* Copyright (C) 2000-2002, HELM Team.
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

(* $Id: proofEngineHelpers.ml 7022 2006-11-15 19:47:41Z fguidi $ *)

(* saturate_term newmeta metasenv context ty goal_arity                       *)
(* Given a type [ty] (a backbone), it returns its suffix of length            *)
(* [goal_arity] head and a new metasenv in which there is new a META for each *)
(* hypothesis, a list of arguments for the new applications and the index of  *)
(* the last new META introduced. The nth argument in the list of arguments is *)
(* just the nth new META.                                                     *)
val saturate_term:
 ?delta: bool -> (* default true *)
 int -> Cic.metasenv -> Cic.context -> Cic.term -> int ->
  Cic.term * Cic.metasenv * Cic.term list * int
