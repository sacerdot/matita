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

include "basic_2/rt_computation/lpxs_lpx.ma".

(* EXTENDED PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS *************)

(* Properties with context-sensitive extended rt-computation for terms ******)

(* Basic_2A1: was: cpxs_bind2 *)
lemma cpxs_bind_alt (G):
      ∀L,V1,V2. ❪G,L❫ ⊢ V1 ⬈* V2 →
      ∀I,T1,T2. ❪G,L.ⓑ[I]V2❫ ⊢ T1 ⬈* T2 →
      ∀p. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬈* ⓑ[p,I]V2.T2.
/4 width=5 by lpxs_cpxs_trans, lpxs_pair, cpxs_bind/ qed.

(* Inversion lemmas with context-sensitive ext rt-computation for terms *****)

lemma cpxs_inv_abst1 (G):
      ∀p,L,V1,T1,U2. ❪G,L❫ ⊢ ⓛ[p]V1.T1 ⬈* U2 →
      ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬈* V2 & ❪G,L.ⓛV1❫ ⊢ T1 ⬈* T2 & U2 = ⓛ[p]V2.T2.
#G #p #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 /2 width=5 by ex3_2_intro/
#U0 #U2 #_ #HU02 * #V0 #T0 #HV10 #HT10 #H destruct
elim (cpx_inv_abst1 … HU02) -HU02 #V2 #T2 #HV02 #HT02 #H destruct
lapply (lpxs_cpx_trans … HT02 (L.ⓛV1) ?)
/3 width=5 by lpxs_pair, cpxs_trans, cpxs_strap1, ex3_2_intro/
qed-.

(* Basic_2A1: was: cpxs_inv_abbr1 *)
lemma cpxs_inv_abbr1_dx (p) (G) (L):
      ∀V1,T1,U2. ❪G,L❫ ⊢ ⓓ[p]V1.T1 ⬈* U2 →
      ∨∨ ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬈* V2 & ❪G,L.ⓓV1❫ ⊢ T1 ⬈* T2 & U2 = ⓓ[p]V2.T2
       | ∃∃T2. ❪G,L.ⓓV1❫ ⊢ T1 ⬈* T2 & ⇧[1] U2 ≘ T2 & p = Ⓣ.
#p #G #L #V1 #T1 #U2 #H
@(cpxs_ind … H) -U2 /3 width=5 by ex3_2_intro, or_introl/
#U0 #U2 #_ #HU02 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpx_inv_abbr1 … HU02) -HU02 *
  [ #V2 #T2 #HV02 #HT02 #H destruct
    lapply (lpxs_cpx_trans … HT02 (L.ⓓV1) ?)
    /4 width=5 by lpxs_pair, cpxs_trans, cpxs_strap1, ex3_2_intro, or_introl/
  | #T2 #HT20 #HTU2 #Hp -V0
    elim (cpx_lifts_sn … HTU2 (Ⓣ) … (L.ⓓV1) … HT20) -T2 [| /3 width=3 by drops_refl, drops_drop/ ] #U0 #HU20 #HTU0
    /4 width=3 by cpxs_strap1, ex3_intro, or_intror/
  ]
| #U1 #HTU1 #HU01 #Hp
  elim (cpx_lifts_sn … HU02 (Ⓣ) … (L.ⓓV1) … HU01) -U0 [| /3 width=3 by drops_refl, drops_drop/ ] #U #HU2 #HU1
  /4 width=3 by cpxs_strap1, ex3_intro, or_intror/
]
qed-.
