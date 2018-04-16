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

include "basic_2/syntax/cl_restricted_weight.ma".
include "basic_2/relocation/lifts_weight_bind.ma".
include "basic_2/relocation/drops.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Forward lemmas with weight for local environments ************************)

(* Basic_2A1: includes: drop_fwd_lw *)
lemma drops_fwd_lw: ∀b,f,L1,L2. ⬇*[b, f] L1 ≘ L2 → ♯{L2} ≤ ♯{L1}.
#b #f #L1 #L2 #H elim H -f -L1 -L2 //
[ /2 width=3 by transitive_le/
| #f #I1 #I2 #L1 #L2 #_ #HI21 #IHL12 normalize
  >(liftsb_fwd_bw … HI21) -HI21 /2 width=1 by monotonic_le_plus_l/
]
qed-.

(* Basic_2A1: includes: drop_fwd_lw_lt *)
lemma drops_fwd_lw_lt: ∀f,L1,L2. ⬇*[Ⓣ, f] L1 ≘ L2 →
                       (𝐈⦃f⦄ → ⊥) → ♯{L2} < ♯{L1}.
#f #L1 #L2 #H elim H -f -L1 -L2
[ #f #Hf #Hnf elim Hnf -Hnf /2 width=1 by/
| /3 width=3 by drops_fwd_lw, le_to_lt_to_lt/
| #f #I1 #I2 #L1 #L2 #_ #HI21 #IHL12 #H normalize in ⊢ (?%%);
  >(liftsb_fwd_bw … HI21) -I2 /5 width=3 by isid_push, monotonic_lt_plus_l/
]
qed-.

(* Forward lemmas with restricted weight for closures ***********************)

(* Basic_2A1: includes: drop_fwd_rfw *)
lemma drops_bind2_fwd_rfw: ∀b,f,I,L,K,V. ⬇*[b, f] L ≘ K.ⓑ{I}V → ∀T. ♯{K, V} < ♯{L, T}.
#b #f #I #L #K #V #HLK lapply (drops_fwd_lw … HLK) -HLK
normalize in ⊢ (%→?→?%%); /3 width=3 by le_to_lt_to_lt, monotonic_lt_plus_r/
qed-.

(* Advanced inversion lemma *************************************************)

lemma drops_inv_x_bind_xy: ∀b,f,I,L. ⬇*[b, f] L ≘ L.ⓘ{I} → ⊥.
#b #f #I #L #H lapply (drops_fwd_lw … H) -b -f
/2 width=4 by lt_le_false/ (**) (* full auto is a bit slow: 19s *)
qed-.
