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

exception MetaSubstFailure of string Lazy.t
exception Uncertain of string Lazy.t
exception AssertFailure of string Lazy.t
exception DeliftingARelWouldCaptureAFreeVariable;;

(* The entry (i,t) in a substitution means that *)
(* (META i) have been instantiated with t.      *)
(* type substitution = (int * (Cic.context * Cic.term)) list *)

  (** @raise SubstNotFound *)

(* apply_subst subst t                     *)
(* applies the substitution [subst] to [t] *)
(* [subst] must be already unwinded        *)

val apply_subst : Cic.substitution -> Cic.term -> Cic.term 
val apply_subst_context : Cic.substitution -> Cic.context -> Cic.context 
val apply_subst_metasenv: Cic.substitution -> Cic.metasenv -> Cic.metasenv 

(*** delifting ***)

val delift : 
  int -> Cic.substitution -> Cic.context -> Cic.metasenv ->
  (Cic.term option) list -> Cic.term ->
    Cic.term * Cic.metasenv * Cic.substitution
val restrict :
  Cic.substitution -> (int * int) list -> Cic.metasenv -> 
  Cic.metasenv * Cic.substitution 

(** delifts the Rels in t of n
 *  @raise DeliftingARelWouldCaptureAFreeVariable
 *)
val delift_rels :
 Cic.substitution -> Cic.metasenv -> int -> Cic.term ->
  Cic.term * Cic.substitution * Cic.metasenv
 
(** {2 Pretty printers} *)
val use_low_level_ppterm_in_context : bool ref
val set_ppterm_in_context :
 (metasenv:Cic.metasenv -> Cic.substitution -> Cic.term -> Cic.context ->
   string) -> unit

val ppsubst_unfolded: metasenv:Cic.metasenv -> Cic.substitution -> string
val ppsubst: metasenv:Cic.metasenv -> Cic.substitution -> string
val ppterm: metasenv:Cic.metasenv -> Cic.substitution -> Cic.term -> string
val ppcontext:
 metasenv:Cic.metasenv -> ?sep: string -> Cic.substitution -> Cic.context ->
   string
val ppterm_in_context:
 metasenv:Cic.metasenv -> Cic.substitution -> Cic.term -> Cic.context -> string
val ppmetasenv: ?sep: string -> Cic.substitution -> Cic.metasenv -> string

(** {2 Format-like pretty printers}
 * As above with prototypes suitable for toplevel/ocamldebug printers. No
 * subsitutions are applied here since such printers are required to be invoked
 * with only one argument.
 *)

val fppsubst: Format.formatter -> Cic.substitution -> unit
val fppterm: Format.formatter -> Cic.term -> unit
val fppmetasenv: Format.formatter -> Cic.metasenv -> unit

(*
(* DEBUG *)
val print_counters: unit -> unit
val reset_counters: unit -> unit
*)

(* val clean_up_meta :
  Cic.substitution -> Cic.metasenv -> Cic.term -> Cic.term
*)
