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

include "static_2/relocation/lifts_lifts_bind.ma".
include "static_2/relocation/drops_weight.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Main properties **********************************************************)

(* Basic_2A1: includes: drop_conf_ge drop_conf_be drop_conf_le *)
theorem drops_conf: ∀b1,f1,L1,L. ⇩*[b1,f1] L1 ≘ L →
                    ∀b2,f,L2. ⇩*[b2,f] L1 ≘ L2 →
                    ∀f2. f1 ⊚ f2 ≘ f → ⇩*[b2,f2] L ≘ L2.
#b1 #f1 #L1 #L #H elim H -f1 -L1 -L
[ #f1 #_ #b2 #f #L2 #HL2 #f2 #Hf12 elim (drops_inv_atom1 … HL2) -b1 -HL2
  #H #Hf destruct @drops_atom
  #H elim (pr_after_inv_isi … Hf12) -Hf12 /2 width=1 by/
| #f1 #I1 #K1 #K #_ #IH #b2 #f #L2 #HL2 #f2 #Hf elim (pr_after_inv_next_sn … Hf) -Hf [2,3: // ]
  #g #Hg #H destruct /3 width=3 by drops_inv_drop1/
| #f1 #I1 #I #K1 #K #_ #HI1 #IH #b2 #f #L2 #HL2 #f2 #Hf elim (pr_after_inv_push_sn … Hf) -Hf [1,3: * |*:// ]
  #g2 #g #Hf #H1 #H2 destruct
  [ elim (drops_inv_skip1 … HL2) -HL2 /3 width=6 by drops_skip, liftsb_div3/
  | /4 width=3 by drops_inv_drop1, drops_drop/
  ]
]
qed-.

(* Basic_1: was: drop1_trans *)
(* Basic_2A1: includes: drop_trans_ge drop_trans_le drop_trans_ge_comm
                        drops_drop_trans
*)
theorem drops_trans: ∀b1,f1,L1,L. ⇩*[b1,f1] L1 ≘ L →
                     ∀b2,f2,L2. ⇩*[b2,f2] L ≘ L2 →
                     ∀f. f1 ⊚ f2 ≘ f → ⇩*[b1∧b2,f] L1 ≘ L2.
#b1 #f1 #L1 #L #H elim H -f1 -L1 -L
[ #f1 #Hf1 #b2 #f2 #L2 #HL2 #f #Hf elim (drops_inv_atom1 … HL2) -HL2
  #H #Hf2 destruct @drops_atom #H elim (andb_inv_true_dx … H) -H
  #H1 #H2 lapply (pr_after_isi_inv_sn … Hf ?) -Hf
  /3 width=3 by pr_isi_eq_repl_back/
| #f1 #I1 #K1 #K #_ #IH #b2 #f2 #L2 #HL2 #f #Hf elim (pr_after_inv_next_sn … Hf) -Hf
  /3 width=3 by drops_drop/
| #f1 #I1 #I #K1 #K #_ #HI1 #IH #b2 #f2 #L2 #HL2 #f #Hf elim (pr_after_inv_push_sn … Hf) -Hf [1,3: * |*: // ]
  #g2 #g #Hg #H1 #H2 destruct
  [ elim (drops_inv_skip1 … HL2) -HL2 /3 width=6 by drops_skip, liftsb_trans/
  | /4 width=3 by drops_inv_drop1, drops_drop/
  ]
]
qed-.

theorem drops_conf_div_isuni:
        ∀f1,L,K. ⇩*[ⓣ,f1] L ≘ K → ∀f2. ⇩*[ⓣ,f2] L ≘ K →
        𝐔❨f1❩ → 𝐔❨f2❩ → f1 ≡ f2.
#f1 #L #K #H elim H -f1 -L -K
[ #f1 #Hf1 #f2 #Hf2 elim (drops_inv_atom1 … Hf2) -Hf2
  /3 width=1 by pr_isi_inv_eq_repl/
| #f1 #I #L #K #Hf1 #IH #f2 elim (pr_map_split_tl f2) *
  #g2 #H2 #Hf2 #HU1 #HU2 destruct
  [ elim (drops_inv_skip1 … Hf2) -IH -HU1 -Hf2 #Y2 #X2 #HY2 #_ #H destruct
    lapply (drops_fwd_isid … HY2 ?) -HY2 /2 width=3 by pr_isu_inv_push/ -HU2
    #H destruct elim (drops_inv_x_bind_xy … Hf1)
  | /4 width=5 by drops_inv_drop1, pr_isu_inv_next, pr_eq_next/
  ]
| #f1 #I1 #I2 #L #K #Hf1 #_ #IH #f2 elim (pr_map_split_tl f2) *
  #g2 #H2 #Hf2 #HU1 #HU2 destruct
  [ elim (drops_inv_skip1 … Hf2) -Hf2 #Y2 #X2 #HY2 #_ #H destruct -Hf1
    /4 width=5 by pr_isu_fwd_push, pr_eq_push/
  | lapply (drops_inv_drop1 … Hf2) -Hf2 -IH -HU2 #Hg2
    lapply (drops_fwd_isid … Hf1 ?) -Hf1 /2 width=3 by pr_isu_inv_push/ -HU1
    #H destruct elim (drops_inv_x_bind_xy … Hg2)
  ]
]
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: includes: drop_mono *)
lemma drops_mono: ∀b1,f,L,L1. ⇩*[b1,f] L ≘ L1 →
                  ∀b2,L2. ⇩*[b2,f] L ≘ L2 → L1 = L2.
#b1 #f #L #L1 lapply (pr_after_isi_dx 𝐢 … f)
/3 width=8 by drops_conf, drops_fwd_isid/
qed-.

lemma drops_inv_uni: ∀L,i. ⇩*[ⓕ,𝐔❨i❩] L ≘ ⋆ → ∀I,K. ⇩[i] L ≘ K.ⓘ[I] → ⊥.
#L #i #H1 #I #K #H2
lapply (drops_F … H2) -H2 #H2
lapply (drops_mono … H2 … H1) -L -i #H destruct
qed-.

lemma drops_ldec_dec: ∀L,i. Decidable (∃∃K,W. ⇩[i] L ≘ K.ⓛW).
#L #i elim (drops_F_uni L i) [| * * [ #I #K1 | * #W1 #K1 ] ]
[4: /3 width=3 by ex1_2_intro, or_introl/
|*: #H1L @or_intror * #K2 #W2 #H2L
    lapply (drops_mono … H2L … H1L) -L #H destruct
]
qed-.

(* Basic_2A1: includes: drop_conf_lt *)
lemma drops_conf_skip1: ∀b2,f,L,L2. ⇩*[b2,f] L ≘ L2 →
                        ∀b1,f1,I1,K1. ⇩*[b1,f1] L ≘ K1.ⓘ[I1] →
                        ∀f2. f1 ⊚ ⫯f2 ≘ f →
                        ∃∃I2,K2. L2 = K2.ⓘ[I2] &
                                 ⇩*[b2,f2] K1 ≘ K2 & ⇧*[f2] I2 ≘ I1.
#b2 #f #L #L2 #H2 #b1 #f1 #I1 #K1 #H1 #f2 #Hf lapply (drops_conf … H1 … H2 … Hf) -L -Hf
#H elim (drops_inv_skip1 … H) -H /2 width=5 by ex3_2_intro/
qed-.

(* Basic_2A1: includes: drop_trans_lt *)
lemma drops_trans_skip2: ∀b1,f1,L1,L. ⇩*[b1,f1] L1 ≘ L →
                         ∀b2,f2,I2,K2. ⇩*[b2,f2] L ≘ K2.ⓘ[I2] →
                         ∀f. f1 ⊚ f2 ≘ ⫯f →
                         ∃∃I1,K1. L1 = K1.ⓘ[I1] &
                                  ⇩*[b1∧b2,f] K1 ≘ K2 & ⇧*[f] I2 ≘ I1.
#b1 #f1 #L1 #L #H1 #b2 #f2 #I2 #K2 #H2 #f #Hf
lapply (drops_trans … H1 … H2 … Hf) -L -Hf
#H elim (drops_inv_skip2 … H) -H /2 width=5 by ex3_2_intro/
qed-.

(* Basic_2A1: includes: drops_conf_div *)
lemma drops_conf_div_bind_isuni:
      ∀f1,f2,I1,I2,L,K.
      ⇩*[ⓣ,f1] L ≘ K.ⓘ[I1] → ⇩*[ⓣ,f2] L ≘ K.ⓘ[I2] →
      𝐔❨f1❩ → 𝐔❨f2❩ → f1 ≡ f2 ∧ I1 = I2.
#f1 #f2 #I1 #I2 #L #K #Hf1 #Hf2 #HU1 #HU2
lapply (drops_isuni_fwd_drop2 … Hf1) // #H1
lapply (drops_isuni_fwd_drop2 … Hf2) // #H2
lapply (drops_conf_div_isuni … H1 … H2 ??) /2 width=3 by pr_isu_next/ -H1 -H2 -HU1 -HU2 #H
lapply (eq_inv_nn … H ????) -H [5: |*: // ] #H12
lapply (drops_eq_repl_back … Hf1 … H12) -Hf1 #H0
lapply (drops_mono … H0 … Hf2) -L #H
destruct /2 width=1 by conj/
qed-.
