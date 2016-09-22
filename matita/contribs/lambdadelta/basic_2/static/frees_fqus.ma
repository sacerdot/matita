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

include "basic_2/relocation/drops_weight.ma".
include "basic_2/s_computation/fqus_weight.ma".
include "basic_2/static/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Properties with star-iterated supclosure *********************************)

lemma frees_fqus_drops: ∀f1,G,L1,T1. L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 →
                        ∀L2,T2. ⦃G, L1, T1⦄ ⊐* ⦃G, L2, T2⦄ →
                        ∀I,n. ⬇*[n] L1 ≡ L2.ⓑ{I}T2 →
                        ∃∃f2. L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 & f2 ⊆ ⫱*[⫯n] f1.
#f1 #G #L1 #T1 #H elim H -f1 -L1 -T1
[ #f1 #J #Hf1 #L2 #T2 #H12 #I #n #HL12
  elim (fqus_inv_atom1 … H12) -H12 #H1 #H2 #H3 destruct
  lapply (drops_fwd_lw … HL12) -HL12 #HL12
  elim (lt_le_false … HL12) -HL12 //
| #f1 #J #L1 #V1 #s #Hf1 #IH #L2 #T2 #H12
  elim (fqus_inv_sort1 … H12) -H12 [ * | #H12 #I * ]
  [ -IH -Hf1 #H1 #H2 #H3 #I #n #HL12 destruct
    lapply (drops_fwd_lw … HL12) -HL12 #HL12
    elim (lt_le_false … HL12) -HL12 //
  | -IH #HL12 lapply (drops_fwd_isid … HL12 ?) -HL12 //
    #H destruct <(fqus_inv_refl_atom3 … H12) -H12 /2 width=3 by sle_refl, ex2_intro/
  | -Hf1 #I #HL12 lapply (drops_inv_drop1 … HL12) -HL12
    #HL12 elim (IH … H12 … HL12) -IH -H12 -HL12 /3 width=3 by ex2_intro/
  ]
| #f1 #J #L1 #V1 #Hf1 #IH #L2 #T2 #H12
  elim (fqus_inv_zero1 … H12) -H12 [ * | #H12 #I * ]
  [ -IH -Hf1 #H1 #H2 #H3 #I #n #HL12 destruct
    lapply (drops_fwd_lw … HL12) -HL12 #HL12
    elim (lt_le_false … HL12) -HL12 //
  | -IH -H12 #HL12 lapply (drops_fwd_isid … HL12 ?) -HL12 //
     #H destruct /3 width=3 by sle_refl, ex2_intro/
  | -Hf1 #n #HL12 lapply (drops_inv_drop1 … HL12) -HL12
    #HL12 elim (IH … H12 … HL12) -IH -H12 -HL12 /3 width=3 by ex2_intro/
  ]
| #f1 #J #L1 #V1 #i #Hf1 #IH #L2 #T2 #H12
  elim (fqus_inv_lref1 … H12) -H12 [ * | #H12 #I * ]
  [ -IH -Hf1 #H1 #H2 #H3 #I #n #HL12 destruct
    lapply (drops_fwd_lw … HL12) -HL12 #HL12
    elim (lt_le_false … HL12) -HL12 //
  | -IH #HL12 lapply (drops_fwd_isid … HL12 ?) -HL12 //
    #H destruct <(fqus_inv_refl_atom3 … H12) -H12 /2 width=3 by sle_refl, ex2_intro/
  | -Hf1 #I #HL12 lapply (drops_inv_drop1 … HL12) -HL12
    #HL12 elim (IH … H12 … HL12) -IH -H12 -HL12 /3 width=3 by ex2_intro/
  ]
| #f1 #J #L1 #V1 #l #Hf1 #IH #L2 #T2 #H12
  elim (fqus_inv_gref1 … H12) -H12 [ * | #H12 #I * ]
  [ -IH -Hf1 #H1 #H2 #H3 #I #n #HL12 destruct
    lapply (drops_fwd_lw … HL12) -HL12 #HL12
    elim (lt_le_false … HL12) -HL12 //
  | -IH #HL12 lapply (drops_fwd_isid … HL12 ?) -HL12 //
    #H destruct <(fqus_inv_refl_atom3 … H12) -H12 /2 width=3 by sle_refl, ex2_intro/
  | -Hf1 #I #HL12 lapply (drops_inv_drop1 … HL12) -HL12
    #HL12 elim (IH … H12 … HL12) -IH -H12 -HL12 /3 width=3 by ex2_intro/
  ]
| #f1V #f1T #f1 #p #J #L1 #V #T #_ #_ #Hf1 #IHV #IHT #L2 #T2 #H12 #I #n #HL12
  elim (fqus_inv_bind1 … H12) -H12 [ * |*: #H12 ]
  [ -IHV -IHT -Hf1 #H1 #H2 #H3 destruct
    lapply (drops_fwd_lw … HL12) -HL12 #HL12
    elim (lt_le_false … HL12) -HL12 //
  | -IHT elim (IHV … H12 … HL12) -IHV -H12 -HL12
    /4 width=6 by sor_tls, sor_sle_sn, ex2_intro/
  | -IHV elim (IHT … H12 I (⫯n)) -IHT -H12 /2 width=1 by drops_drop/ -HL12
    <tls_xn /4 width=6 by ex2_intro, sor_tls, sor_sle_dx/
  ]
| #f1V #f1T #f1 #J #L1 #V #T #_ #_ #Hf1 #IHV #IHT #L2 #T2 #H12 #I #n #HL12
  elim (fqus_inv_flat1 … H12) -H12 [ * |*: #H12 ]
  [ -IHV -IHT -Hf1 #H1 #H2 #H3 destruct
    lapply (drops_fwd_lw … HL12) -HL12 #HL12
    elim (lt_le_false … HL12) -HL12 //
  | -IHT elim (IHV … H12 … HL12) -IHV -H12 -HL12
    /4 width=6 by sor_tls, sor_sle_sn, ex2_intro/
  | -IHV elim (IHT … H12 … HL12) -IHT -H12 -HL12
    /4 width=6 by ex2_intro, sor_tls, sor_sle_dx/
  ]
]
qed-.
