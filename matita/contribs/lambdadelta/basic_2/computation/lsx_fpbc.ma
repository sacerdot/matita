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

include "basic_2/computation/lpxs_lpxs.ma".
include "basic_2/computation/fpbs.ma".
include "basic_2/computation/fpbc.ma".
include "basic_2/computation/csx_lift.ma".
include "basic_2/computation/csx_lpxs.ma".
include "basic_2/computation/lsx_csx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced eliminators for context-sensitive ext. strongly norm. terms *****)

lemma tollens: ∀R1,R2,R3:Prop. (R1 → R2) → (R2 → R3) → R1 → R3.
/3 width=1/ qed-.

axiom fqus_lpxs_trans_nlleq: ∀h,g,G1,G2,K1,K2,T1,T2. ⦃G1, K1, T1⦄ ⊃* ⦃G2, K2, T2⦄ →
                             ∀L2. ⦃G2, K2⦄ ⊢ ➡*[h, g] L2 → (K2 ⋕[O, T2] L2 →⊥) →
                             ∃∃L1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 &
                                   K1 ⋕[O, T1] L1 → ⊥ & ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄.

axiom fpbs_lpxs_trans_nlleq: ∀h,g,G1,G2,K1,K2,T1,T2. ⦃G1, K1, T1⦄ ≥[h, g] ⦃G2, K2, T2⦄ →
                             ∀L2. ⦃G2, K2⦄ ⊢ ➡*[h, g] L2 → (K2 ⋕[O, T2] L2 →⊥) →
                             ∃∃L1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 &
                                   K1 ⋕[O, T1] L1 → ⊥ & ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.


lemma csx_ind_fpbc_fpbs: ∀h,g. ∀R:relation3 genv lenv term.
                         (∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                                     (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                     R G1 L1 T1
                         ) →
                         ∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                         ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                         R G2 L2 T2.
#h #g #R #IH1 #G1 #L1 #T1 #H @(csx_ind_alt … H) -T1
#T1 #HT1 @(lsx_ind h g T1 G1 … L1) /2 width=1 by csx_lsx/ -L1
#L1 @(fqup_wf_ind … G1 L1 T1) -G1 -L1 -T1
#G1 #L1 #T1 #IH2 #H1 #IH3 #IH4 #G2 #L2 #T2 #H12
@IH1 -IH1 (* /4 width=5 by lsx_inv_csx, csx_lpxs_conf, csx_fqus_conf/ *)
[2: #G #L #T *
    [
    |
    | #L0 #HL20 #HnT2 elim (fpbs_lpxs_trans_nlleq … H12 … HL20 HnT2) -L2
      #L2 #HL12 #HnT1 #H12 @(IH3 … HL12 HnT1 … H12) -IH3
      #H26 #H27 #H28 #H29 #H30 #H31 #H32
      @(IH4) … H27 H28) 
      
  [ #H12 #H13 #H14 #H15 #H16 #H17 #H18 #H19 #H20 #H21 #H22 #H23 #H24
    lapply (fqup_fqus_trans … H15 … H21) -H15 -H21 #H
    @(IH3 … H23 H24) 
  
  #H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8 #H9 #H10
  @(IH4 … H3 … H10) -IH4 -H10 -H3 //



 [ -IH4 | -H1 -IH2 -IH4 | -H1 -H2 -IH2 -IH3 ]
[ #G0 #L0 #T0 #H20 elim (lpxs_lleq_fqup_trans … H20 … HYL2 HT2) -L2
  #L2 #H20 #HL20 lapply (fqus_fqup_trans … H12 H20) -G2 -Y -T2
  #H10 @(IH2 … H10) -IH2 /2 width=5 by csx_fqup_conf/
(*  
  #T2 #HT02 #H #G3 #L3 #T3 #HT23 elim (fqup_cpxs_trans_neq … H10 … HT02 H) -T0
  /4 width=8 by fqup_fqus_trans, fqup_fqus/
*)
| (* #T0 #HT20 #H elim (fqus_cpxs_trans_neq … H12 … HT20 H) -T2 /3 width=4 by/ *)
| #L0 #HL20 #HnT2 @(IH4 L0) /3 width=3 by lpxs_trans, lleq_canc_sn/



 
  
  | /3 width=3 by /
  [ /2 width=3

 lapply (lpxs_trans … HYL2 … HL20)
  #HYL0 lapply (tollens ???? HnT2) [ @(lleq_canc_sn … HT2) | skip ] -L2
  #HnT2 elim (fqus_lpxs_trans_nlleq … H12 … HYL0 HnT2)      - 
  
  
  lapply (lleq_canc_sn … L0 … HT2)



  | 

elim (lpxs_lleq_fqup_trans … H12 … HYL2 HT2) -L2
  
   
]
qed-.

lemma csx_ind_fpbc: ∀h,g. ∀R:relation3 genv lenv term.
                    (∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                                (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                R G1 L1 T1
                    ) →
                    ∀G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → R G L T.
/4 width=8 by csx_ind_fpbc_fqus/ qed-.
