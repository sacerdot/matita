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

include "ground/relocation/gr_id_eq.ma".
include "ground/relocation/gr_pat_eq.ma".

(* POSITIVE APPLICATION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties on id ************************************************)

(*** id_at *)
lemma gr_pat_id (i): @❪i,𝐢❫ ≘ i.
/2 width=1 by gr_pat_eq, gr_eq_refl/ qed.

(* Inversions with id *)

(*** id_inv_at *)
lemma gr_pat_inv_id (f):
      (∀i. @❪i,f❫ ≘ i) → 𝐢 ≡ f.
/3 width=1 by gr_pat_inv_eq, gr_id_eq/
qed-.
