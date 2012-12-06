(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "redex_pointer.ma".

(* REDEX POINTER SEQUENCE ***************************************************)

(* Policy: pointer sequence metavariables: r, s *)

definition rpseq: Type[0] \def list rptr.

(* Note: a "spine" computation contracts just redexes in the spine *)
definition is_spine: predicate rpseq ≝ λs.
                     All … in_spine s.

(* Note: to us, a "normal" computation contracts redexes in non-decreasing positions *)
definition is_le: predicate rpseq ≝ λs.
                  Allr … rple s.

(* Note: a normal spine computation *)
definition is_spine_le: predicate rpseq ≝ λs.
                        is_spine s ∧ is_le s.
