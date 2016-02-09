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

include "basic_2/grammar/cl_restricted_weight.ma".
include "basic_2/relocation/lifts_weight.ma".
include "basic_2/relocation/drops.ma".

(* GENERAL SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Forward lemmas on weight for local environments **************************)

(* Basic_2A1: includes: drop_fwd_lw *)
lemma drops_fwd_lw: ∀L1,L2,c,f. ⬇*[c, f] L1 ≡ L2 → ♯{L2} ≤ ♯{L1}.
#L1 #L2 #c #f #H elim H -L1 -L2 -f //
[ /2 width=3 by transitive_le/
| #I #L1 #L2 #V1 #V2 #f #_ #HV21 #IHL12 normalize
  >(lifts_fwd_tw … HV21) -HV21 /2 width=1 by monotonic_le_plus_l/
]
qed-.

(* Basic_2A1: includes: drop_fwd_lw_lt *)
(* Note: 𝐈⦃t⦄ → ⊥ is ∥l∥ < |L| *)
lemma drops_fwd_lw_lt: ∀L1,L2,f. ⬇*[Ⓣ, f] L1 ≡ L2 →
                       (𝐈⦃f⦄ → ⊥) → ♯{L2} < ♯{L1}.
#L1 #L2 #f #H elim H -L1 -L2 -f
[ #f #Hf #Hnf elim Hnf -Hnf /2 width=1 by/
| /3 width=3 by drops_fwd_lw, le_to_lt_to_lt/
| #I #L1 #L2 #V1 #V2 #f #_ #HV21 #IHL12 #H normalize in ⊢ (?%%); -I
  >(lifts_fwd_tw … HV21) -V2 /5 width=1 by isid_push, monotonic_lt_plus_l/
]
qed-.

(* Forward lemmas on restricted weight for closures *************************)

(* Basic_2A1: includes: drop_fwd_rfw *)
lemma drops_pair2_fwd_rfw: ∀I,L,K,V,c,f. ⬇*[c, f] L ≡ K.ⓑ{I}V → ∀T. ♯{K, V} < ♯{L, T}.
#I #L #K #V #c #f #HLK lapply (drops_fwd_lw … HLK) -HLK
normalize in ⊢ (%→?→?%%); /3 width=3 by le_to_lt_to_lt/
qed-.
