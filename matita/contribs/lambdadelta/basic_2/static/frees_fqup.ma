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

include "basic_2/relocation/drops.ma".
include "basic_2/s_computation/fqup_weight.ma".
include "basic_2/static/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

(* Note: this replaces lemma 1400 concluding the "big tree" theorem *)
lemma frees_total: ∀L,T. ∃f. L ⊢ 𝐅*⦃T⦄ ≡ f.
#L #T @(fqup_wf_ind_eq … (⋆) L T) -L -T
#G0 #L0 #T0 #IH #G #L *
[ cases L -L /3 width=2 by frees_atom, ex_intro/
  #L #I #V *
  [ #s #HG #HL #HT destruct
    elim (IH G L (⋆s)) -IH /3 width=2 by frees_sort_gen, fqu_fqup, fqu_drop, lifts_sort, ex_intro/
  | * [2: #i ] #HG #HL #HT destruct
    [ elim (IH G L (#i)) -IH /3 width=2 by frees_lref, fqu_fqup, ex_intro/
    | elim (IH G L V) -IH /3 width=2 by frees_zero, fqu_fqup, fqu_lref_O, ex_intro/
    ]
  | #l #HG #HL #HT destruct
    elim (IH G L (§l)) -IH /3 width=2 by frees_gref_gen, fqu_fqup, fqu_drop, lifts_gref, ex_intro/
  ]
| * [ #p ] #I #V #T #HG #HL #HT destruct elim (IH G L V) // #f1 #HV
  [ elim (IH G (L.ⓑ{I}V) T) -IH // #f2 #HT
    elim (sor_isfin_ex f1 (⫱f2))
    /3 width=6 by frees_fwd_isfin, frees_bind, isfin_tl, ex_intro/
  | elim (IH G L T) -IH // #f2 #HT
    elim (sor_isfin_ex f1 f2)
    /3 width=6 by frees_fwd_isfin, frees_flat, ex_intro/ 
  ]
]
qed-.

(* Properties with plus-iterated supclosure *********************************)

lemma frees_drops_next: ∀f1,L1,T1. L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 →
                        ∀I2,L2,V2,n. ⬇*[n] L1 ≡ L2.ⓑ{I2}V2 →
                        ∀g1. ⫯g1 = ⫱*[n] f1 →
                        ∃∃g2. L2 ⊢ 𝐅*⦃V2⦄ ≡ g2 & g2 ⊆ g1.
#f1 #L1 #T1 #H elim H -f1 -L1 -T1
[ #f1 #I1 #Hf1 #I2 #L2 #V2 #n #HL12
  elim (drops_inv_atom1 … HL12) -HL12 #H destruct
| #f1 #I1 #L1 #V1 #s #_ #IH #I2 #L2 #V2 *
  [ -IH #_ #g1 #Hgf1 elim (discr_next_push … Hgf1)
  | #n #HL12 lapply (drops_inv_drop1 … HL12) -HL12
    #HL12 #g1 <tls_xn #Hgf1 elim (IH … HL12 … Hgf1) -IH -HL12 -Hgf1
    /2 width=3 by ex2_intro/
  ]
| #f1 #I1 #L1 #V1 #Hf1 #IH #I2 #L2 #V2 *
  [ -IH #HL12 lapply (drops_fwd_isid … HL12 ?) -HL12 //
    #H destruct #g1 #Hgf1 >(injective_next … Hgf1) -g1
    /3 width=3 by sle_refl, ex2_intro/
  | -Hf1 #n #HL12 lapply (drops_inv_drop1 … HL12) -HL12
    #HL12 #g1 <tls_xn <tl_next_rew #Hgf1 elim (IH … HL12 … Hgf1) -IH -HL12 -Hgf1
    /2 width=3 by ex2_intro/
  ]
| #f1 #I1 #L1 #V1 #i #_ #IH #I2 #L2 #V2 *
  [ -IH #_ #g1 #Hgf1 elim (discr_next_push … Hgf1)
  | #n #HL12 lapply (drops_inv_drop1 … HL12) -HL12
    #HL12 #g1 <tls_xn #Hgf1 elim (IH … HL12 … Hgf1) -IH -HL12 -Hgf1
    /2 width=3 by ex2_intro/
  ]
| #f1 #I1 #L1 #V1 #l #_ #IH #I2 #L2 #V2 *
  [ -IH #_ #g1 #Hgf1 elim (discr_next_push … Hgf1)
  | #n #HL12 lapply (drops_inv_drop1 … HL12) -HL12
    #HL12 #g1 <tls_xn #Hgf1 elim (IH … HL12 … Hgf1) -IH -HL12 -Hgf1
    /2 width=3 by ex2_intro/
  ]
| #fV1 #fT1 #f1 #p #I1 #L1 #V1 #T1 #_ #_ #Hf1 #IHV1 #IHT1 #I2 #L2 #V2 #n #HL12 #g1 #Hgf1
  lapply (sor_tls … Hf1 n) -Hf1 <Hgf1 -Hgf1 #Hf1
  elim (sor_xxn_tl … Hf1) [1,2: * |*: // ] -Hf1
  #gV1 #gT1 #Hg1
  [ -IHT1 #H1 #_ elim (IHV1 … HL12 … H1) -IHV1 -HL12 -H1
    /3 width=6 by sor_inv_sle_sn_trans, ex2_intro/
  | -IHV1 #_ >tls_xn #H2 elim (IHT1 … H2) -IHT1 -H2
    /3 width=6 by drops_drop, sor_inv_sle_dx_trans, ex2_intro/
  ]
| #fV1 #fT1 #f1 #I1 #L1 #V1 #T1 #_ #_ #Hf1 #IHV1 #IHT1 #I2 #L2 #V2 #n #HL12 #g1 #Hgf1
  lapply (sor_tls … Hf1 n) -Hf1 <Hgf1 -Hgf1 #Hf1
  elim (sor_xxn_tl … Hf1) [1,2: * |*: // ] -Hf1
  #gV1 #gT1 #Hg1
  [ -IHT1 #H1 #_ elim (IHV1 … HL12 … H1) -IHV1 -HL12 -H1
    /3 width=6 by sor_inv_sle_sn_trans, ex2_intro/
  | -IHV1 #_ #H2 elim (IHT1 … HL12 … H2) -IHT1 -HL12 -H2
    /3 width=6 by sor_inv_sle_dx_trans, ex2_intro/
  ]
]
qed-.
