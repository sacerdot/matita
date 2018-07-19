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

include "static_2/relocation/lifts_lifts.ma".
include "apps_2/functional/flifts.ma".

(* GENERIC FUNCTIONAL RELOCATION ********************************************)

(* Main derived properties **************************************************)

theorem flifts_compose (f2) (f1) (T): ↑*[f2]↑*[f1]T = ↑*[f2∘f1]T.
#f2 #f1 #T
elim (lifts_total T f1) #U #HTU
>(flifts_inv_lifts … HTU)
/4 width=6 by flifts_inv_lifts, lifts_trans, sym_eq/
qed.

(* Main derived properties with uniform relocation **************************)

theorem flifts_compose_uni (l2) (l1) (T): ↑[l2]↑[l1]T = ↑[l2+l1]T.
#l2 #l1 #T >flifts_compose
/4 width=1 by flifts_inv_lifts, lifts_uni, sym_eq/ qed.
