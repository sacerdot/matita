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

exception Parse_error of string
exception Level_not_found of int

type checked_l1_pattern = private CL1P of CicNotationPt.term * int

(** {2 Parsing functions} *)

  (** concrete syntax pattern: notation level 1, the 
   *  integer is the precedence *)
val parse_level1_pattern: int -> Ulexing.lexbuf -> CicNotationPt.term

  (** AST pattern: notation level 2 *)
val parse_level2_ast: Ulexing.lexbuf -> CicNotationPt.term
val parse_level2_meta: Ulexing.lexbuf -> CicNotationPt.term

(** {2 Grammar extension} *)

type rule_id

val compare_rule_id : rule_id -> rule_id -> int

val check_l1_pattern: (* level1_pattern, pponly, precedence, assoc *)
 CicNotationPt.term -> bool ->  int -> Gramext.g_assoc -> checked_l1_pattern

val extend:
  checked_l1_pattern ->
  (CicNotationEnv.t -> CicNotationPt.location -> CicNotationPt.term) ->
    rule_id

val delete: rule_id -> unit

(** {2 Grammar entries}
 * needed by grafite parser *)

val level2_ast_grammar: unit -> Grammar.g

val term : unit -> CicNotationPt.term Grammar.Entry.e

val let_defs : unit ->
  (CicNotationPt.term CicNotationPt.capture_variable list * CicNotationPt.term CicNotationPt.capture_variable * CicNotationPt.term * int) list
    Grammar.Entry.e

val protected_binder_vars : unit ->
  (CicNotationPt.term list * CicNotationPt.term option) Grammar.Entry.e

val parse_term: Ulexing.lexbuf -> CicNotationPt.term

(** {2 Debugging} *)

  (** print "level2_pattern" entry on stdout, flushing afterwards *)
val print_l2_pattern: unit -> unit

val push: unit -> unit
val pop: unit -> unit
