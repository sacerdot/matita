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

include "basic_2/multiple/fqup.ma".
include "basic_2/multiple/frees_lift.ma".
include "basic_2/reduction/lpx_ldrop.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)
(*
lemma cofrees_lsuby_conf: ∀L1,U,i. L1 ⊢ i ~ϵ 𝐅*⦃U⦄ →
                          ∀L2. lsuby L1 L2 → L2 ⊢ i ~ϵ 𝐅*⦃U⦄.
/3 width=3 by lsuby_cpys_trans/ qed-.

lemma lpx_cpx_cofrees_conf: ∀h,g,G,L1,U1,U2. ⦃G, L1⦄ ⊢ U1 ➡[h, g] U2 →
                            ∀L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 →
                            ∀i. L1 ⊢ i ~ϵ 𝐅*⦃U1⦄ → L2 ⊢ i ~ϵ 𝐅*⦃U2⦄.
#h #g #G #L1 #U1 @(fqup_wf_ind_eq … G L1 U1) -G -L1 -U1
#G0 #L0 #U0 #IH #G #L1 * *
[ -IH #k #HG #HL #HU #U2 #H elim (cpx_inv_sort1 … H) -H
  [| * #l #_ ] #H destruct //
| #j #HG #HL #HU #U2 #H #L2 #HL12 #i #Hi elim (cpx_inv_lref1 … H) -H
  [ #H destruct elim (lt_or_eq_or_gt i j) #Hji
    [ -IH -HL12 /2 width=4 by cofrees_lref_gt/
    | -IH -HL12 destruct elim (cofrees_inv_lref_eq … Hi)
    | elim (lt_or_ge j (|L2|)) /2 width=5 by cofrees_lref_free/ #Hj
      elim (ldrop_O1_lt (Ⓕ) L1 j) [2: >(lpx_fwd_length … HL12) // ] #I #K1 #W1 #HLK1
      elim (lpx_ldrop_conf … HLK1 … HL12) -HL12 #Y #H #HLK2
      elim (lpx_inv_pair1 … H) -H #K2 #W2 #HK12 #HW12 #H destruct
      lapply (cofrees_inv_lref_lt … Hi … HLK1) -Hi // #HW1
      lapply (IH … HW12 … HK12 … HW1) /2 width=2 by fqup_lref/ -L1 -K1 -W1 #HW2
      /2 width=9 by cofrees_lref_lt/ (**) (* full auto too slow *)
    ]
  | * #I #K1 #W1 #W0 #HLK1 #HW10 #HW0U2 elim (lt_or_ge j i) #Hji
    [ lapply (ldrop_fwd_drop2 … HLK1) #H0
      elim (lpx_ldrop_conf … H0 … HL12) #K2 #HK12 #HLK2
      @(cofrees_lift_ge … HLK2 … HW0U2) //
      @(IH … HW10) /2 width=2 by fqup_lref/ -L2 -K2 -W0 -U2 -IH
      <minus_plus /2 width=7 by cofrees_inv_lref_lt/
    | -IH lapply (ldrop_fwd_drop2 … HLK1) -HLK1 #HLK1
      elim (lpx_ldrop_conf … HLK1 … HL12) -I -L1 -W1
      /2 width=12 by cofrees_lift_be/
    ]
  ]
| -IH #p #HG #HL #HU #U2 #H lapply (cpx_inv_gref1 … H) -H
  #H destruct //
| #a #I #W1 #U1 #HG #HL #HU #X #HX #L2 #HL12 #i #Hi destruct
  elim (cofrees_inv_bind … Hi) -Hi #HW1 #HU1
  elim (cpx_inv_bind1 … HX) -HX
  [ * #W2 #U2 #HW12 #HU12 #H destruct /4 width=8 by cofrees_bind, lpx_pair/
  |
  ]
| #I #W1 #X1 #HG #HL #HU #X2 #HX2 #L2 #HL12 #i #Hi destruct
  elim (cofrees_inv_flat … Hi) -Hi #HW1 #HX1
  elim (cpx_inv_flat1 … HX2) -HX2 *
  [ #W2 #U2 #HW12 #HU12 #H destruct /3 width=7 by cofrees_flat/
  | #HU12 #H destruct /2 width=7 by/
  | #HW12 #H destruct /2 width=7 by/
  | #b #W2 #V1 #V2 #U1 #U2 #HW12 #HV12 #HU12 #H1 #H2 #H3 destruct
    elim (cofrees_inv_bind … HX1) -HX1 #HV1 #HU1
    @cofrees_bind [ /3 width=7 by cofrees_flat/ ]
    @(cofrees_lsuby_conf (L2.ⓛV2)) /3 width=7 by lpx_pair, lsuby_succ/
  | 
    
   
*)
