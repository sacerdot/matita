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

include "basic_2/syntax/lenv_length.ma".
include "basic_2/relocation/drops.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Forward lemmas with length for local environments ************************)

(* Basic_2A1: includes: drop_fwd_length_le4 *)
lemma drops_fwd_length_le4: ∀b,f,L1,L2. ⬇*[b, f] L1 ≡ L2 → |L2| ≤ |L1|.
#b #f #L1 #L2 #H elim H -f -L1 -L2 /2 width=1 by le_S, le_S_S/
qed-.

(* Basic_2A1: includes: drop_fwd_length_eq1 *)
theorem drops_fwd_length_eq1: ∀b1,b2,f,L1,K1. ⬇*[b1, f] L1 ≡ K1 →
                              ∀L2,K2. ⬇*[b2, f] L2 ≡ K2 →
                              |L1| = |L2| → |K1| = |K2|.
#b1 #b2 #f #L1 #K1 #HLK1 elim HLK1 -f -L1 -K1
[ #f #_ #L2 #K2 #HLK2 #H lapply (length_inv_zero_sn … H) -H
  #H destruct elim (drops_inv_atom1 … HLK2) -HLK2 //
| #f #I1 #L1 #K1 #_ #IH #X2 #K2 #HX #H elim (length_inv_succ_sn … H) -H
  #I2 #L2 #H12 #H destruct lapply (drops_inv_drop1 … HX) -HX
  #HLK2 @(IH … HLK2 H12) (**) (* auto fails *)
| #f #I1 #I2 #L1 #K1 #_ #_ #IH #X2 #Y2 #HX #H elim (length_inv_succ_sn … H) -H
  #I2 #L2 #H12 #H destruct elim (drops_inv_skip1 … HX) -HX
  #I2 #K2 #HLK2 #_ #H destruct
  lapply (IH … HLK2 H12) -f >length_bind >length_bind /2 width=1 by/ (**) (* full auto fails *)
]
qed-.  

(* forward lemmas with finite colength assignment ***************************)

lemma drops_fwd_fcla: ∀f,L1,L2. ⬇*[Ⓣ, f] L1 ≡ L2 →
                      ∃∃n. 𝐂⦃f⦄ ≡ n & |L1| = |L2| + n.
#f #L1 #L2 #H elim H -f -L1 -L2
[ /4 width=3 by fcla_isid, ex2_intro/
| #f #I #L1 #L2 #_ * >length_bind /3 width=3 by fcla_next, ex2_intro, eq_f/
| #f #I1 #I2 #L1 #L2 #_ #_ * >length_bind >length_bind /3 width=3 by fcla_push, ex2_intro/
]
qed-.

(* Basic_2A1: includes: drop_fwd_length *)
lemma drops_fcla_fwd: ∀f,L1,L2,n. ⬇*[Ⓣ, f] L1 ≡ L2 → 𝐂⦃f⦄ ≡ n →
                      |L1| = |L2| + n.
#f #l1 #l2 #n #Hf #Hn elim (drops_fwd_fcla … Hf) -Hf
#k #Hm #H <(fcla_mono … Hm … Hn) -f //
qed-.

lemma drops_fwd_fcla_le2: ∀f,L1,L2. ⬇*[Ⓣ, f] L1 ≡ L2 →
                          ∃∃n. 𝐂⦃f⦄ ≡ n & n ≤ |L1|.
#f #L1 #L2 #H elim (drops_fwd_fcla … H) -H /2 width=3 by ex2_intro/
qed-.

(* Basic_2A1: includes: drop_fwd_length_le2 *)
lemma drops_fcla_fwd_le2: ∀f,L1,L2,n. ⬇*[Ⓣ, f] L1 ≡ L2 → 𝐂⦃f⦄ ≡ n →
                          n ≤ |L1|.
#f #L1 #L2 #n #H #Hn elim (drops_fwd_fcla_le2 … H) -H
#k #Hm #H <(fcla_mono … Hm … Hn) -f //
qed-.

lemma drops_fwd_fcla_lt2: ∀f,L1,I2,K2. ⬇*[Ⓣ, f] L1 ≡ K2.ⓘ{I2} →
                          ∃∃n. 𝐂⦃f⦄ ≡ n & n < |L1|.
#f #L1 #I2 #K2 #H elim (drops_fwd_fcla … H) -H
#n #Hf #H >H -L1 /3 width=3 by le_S_S, ex2_intro/
qed-.

(* Basic_2A1: includes: drop_fwd_length_lt2 *)
lemma drops_fcla_fwd_lt2: ∀f,L1,I2,K2,n.
                          ⬇*[Ⓣ, f] L1 ≡ K2.ⓘ{I2} → 𝐂⦃f⦄ ≡ n →
                          n < |L1|.
#f #L1 #I2 #K2 #n #H #Hn elim (drops_fwd_fcla_lt2 … H) -H
#k #Hm #H <(fcla_mono … Hm … Hn) -f //
qed-.

(* Basic_2A1: includes: drop_fwd_length_lt4 *)
lemma drops_fcla_fwd_lt4: ∀f,L1,L2,n. ⬇*[Ⓣ, f] L1 ≡ L2 → 𝐂⦃f⦄ ≡ n → 0 < n →
                          |L2| < |L1|.
#f #L1 #L2 #n #H #Hf #Hn lapply (drops_fcla_fwd … H Hf) -f
/2 width=1 by lt_minus_to_plus_r/ qed-.

(* Basic_2A1: includes: drop_inv_length_eq *)
lemma drops_inv_length_eq: ∀f,L1,L2. ⬇*[Ⓣ, f] L1 ≡ L2 → |L1| = |L2| → 𝐈⦃f⦄.
#f #L1 #L2 #H #HL12 elim (drops_fwd_fcla … H) -H
#n #Hn <HL12 -L2 #H lapply (discr_plus_x_xy … H) -H
/2 width=3 by fcla_inv_xp/
qed-.

(* Basic_2A1: includes: drop_fwd_length_eq2 *)
theorem drops_fwd_length_eq2: ∀f,L1,L2,K1,K2. ⬇*[Ⓣ, f] L1 ≡ K1 → ⬇*[Ⓣ, f] L2 ≡ K2 →
                              |K1| = |K2| → |L1| = |L2|.
#f #L1 #L2 #K1 #K2 #HLK1 #HLK2 #HL12
elim (drops_fwd_fcla … HLK1) -HLK1 #n1 #Hn1 #H1 >H1 -L1
elim (drops_fwd_fcla … HLK2) -HLK2 #n2 #Hn2 #H2 >H2 -L2
<(fcla_mono … Hn2 … Hn1) -f //
qed-.

theorem drops_conf_div: ∀f1,f2,L1,L2. ⬇*[Ⓣ, f1] L1 ≡ L2 → ⬇*[Ⓣ, f2] L1 ≡ L2 →
                        ∃∃n. 𝐂⦃f1⦄ ≡ n & 𝐂⦃f2⦄ ≡ n.
#f1 #f2 #L1 #L2 #H1 #H2
elim (drops_fwd_fcla … H1) -H1 #n1 #Hf1 #H1
elim (drops_fwd_fcla … H2) -H2 #n2 #Hf2 >H1 -L1 #H
lapply (injective_plus_r … H) -L2 #H destruct /2 width=3 by ex2_intro/
qed-.

theorem drops_conf_div_fcla: ∀f1,f2,L1,L2,n1,n2.
                             ⬇*[Ⓣ, f1] L1 ≡ L2 → ⬇*[Ⓣ, f2] L1 ≡ L2 → 𝐂⦃f1⦄ ≡ n1 → 𝐂⦃f2⦄ ≡ n2 →
                             n1 = n2.
#f1 #f2 #L1 #L2 #n1 #n2 #Hf1 #Hf2 #Hn1 #Hn2
lapply (drops_fcla_fwd … Hf1 Hn1) -f1 #H1
lapply (drops_fcla_fwd … Hf2 Hn2) -f2 >H1 -L1
/2 width=1 by injective_plus_r/
qed-.
