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

include "ground/notation/functions/subset_p_0.ma".
include "ground/lib/subset.ma".
include "ground/arith/nat_succ.ma".
include "ground/arith/nat_ppred_psucc.ma".
include "ground/arith/nat_pred.ma".

(* PREDECESSOR FOR NON-NEGATIVE INTEGERS ************************************)

definition nispos: 𝒫❨ℕ❩ ≝
           {n | n = (⁤↑⫰n)}.

interpretation
  "positivity predicate (non-negative integers)"
  'SubsetP = (nispos).

(* Constructions with nsucc *************************************************)

lemma nispos_intro (n):
      n = (⁤↑⫰n) → n ϵ 𝐏.
// qed-.

lemma nsucc_pred (p):
      (⁤p) ϵ 𝐏.
// qed.

(*** pred_Sn pred_S *)
lemma npred_succ (n): n = ⫰(⁤↑n).
//
qed.

(* Inversions with nsucc ****************************************************)

(*** nat_split *)
lemma nat_split_zero_pos (n): ∨∨ 𝟎 = n | n ϵ 𝐏.
#n @(nat_ind_succ … n) -n
/2 width=1 by or_introl, or_intror/
qed-.
