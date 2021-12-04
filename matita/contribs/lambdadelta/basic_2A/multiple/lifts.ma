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

include "ground/relocation/mr2_at.ma".
include "ground/relocation/mr2_plus.ma".
include "basic_2A/notation/relations/rliftstar_3.ma".
include "basic_2A/substitution/lift.ma".

(* GENERIC TERM RELOCATION **************************************************)

inductive lifts: mr2 → relation term ≝
| lifts_nil : ∀T. lifts (𝐞) T T
| lifts_cons: ∀T1,T,T2,cs,l,m.
              ⬆[l,m] T1 ≡ T → lifts cs T T2 → lifts (❨l, m❩; cs) T1 T2
.

interpretation "generic relocation (term)"
   'RLiftStar cs T1 T2 = (lifts cs T1 T2).

(* Basic inversion lemmas ***************************************************)

fact lifts_inv_nil_aux: ∀T1,T2,cs. ⬆*[cs] T1 ≡ T2 → cs = 𝐞 → T1 = T2.
#T1 #T2 #cs * -T1 -T2 -cs //
#T1 #T #T2 #l #m #cs #_ #_ #H destruct
qed-.

lemma lifts_inv_nil: ∀T1,T2. ⬆*[𝐞] T1 ≡ T2 → T1 = T2.
/2 width=3 by lifts_inv_nil_aux/ qed-.

fact lifts_inv_cons_aux: ∀T1,T2,cs. ⬆*[cs] T1 ≡ T2 →
                         ∀l,m,tl. cs = ❨l, m❩; tl →
                         ∃∃T. ⬆[l, m] T1 ≡ T & ⬆*[tl] T ≡ T2.
#T1 #T2 #cs * -T1 -T2 -cs
[ #T #l #m #tl #H destruct
| #T1 #T #T2 #cs #l #m #HT1 #HT2 #l0 #m0 #tl #H destruct
  /2 width=3 by ex2_intro/
qed-.

lemma lifts_inv_cons: ∀T1,T2,l,m,cs. ⬆*[❨l, m❩; cs] T1 ≡ T2 →
                      ∃∃T. ⬆[l, m] T1 ≡ T & ⬆*[cs] T ≡ T2.
/2 width=3 by lifts_inv_cons_aux/ qed-.

lemma lifts_inv_sort1: ∀T2,k,cs. ⬆*[cs] ⋆k ≡ T2 → T2 = ⋆k.
#T2 #k #cs elim cs -cs
[ #H <(lifts_inv_nil … H) -H //
| #l #m #cs #IH #H
  elim (lifts_inv_cons … H) -H #X #H
  >(lift_inv_sort1 … H) -H /2 width=1 by/
]
qed-.

lemma lifts_inv_lref1: ∀T2,cs,i1. ⬆*[cs] #i1 ≡ T2 →
                       ∃∃i2. @❪i1, cs❫ ≘ i2 & T2 = #i2.
#T2 #cs elim cs -cs
[ #i1 #H <(lifts_inv_nil … H) -H /2 width=3 by at_nil, ex2_intro/
| #l #m #cs #IH #i1 #H
  elim (lifts_inv_cons … H) -H #X #H1 #H2
  elim (lift_inv_lref1 … H1) -H1 * #Hli1 #H destruct
  elim (IH … H2) -IH -H2 /3 width=3 by at_lt, at_ge, ex2_intro/
]
qed-.

lemma lifts_inv_gref1: ∀T2,p,cs. ⬆*[cs] §p ≡ T2 → T2 = §p.
#T2 #p #cs elim cs -cs
[ #H <(lifts_inv_nil … H) -H //
| #l #m #cs #IH #H
  elim (lifts_inv_cons … H) -H #X #H
  >(lift_inv_gref1 … H) -H /2 width=1 by/
]
qed-.

lemma lifts_inv_bind1: ∀a,I,T2,cs,V1,U1. ⬆*[cs] ⓑ{a,I} V1. U1 ≡ T2 →
                       ∃∃V2,U2. ⬆*[cs] V1 ≡ V2 & ⬆*[cs + 1] U1 ≡ U2 &
                                T2 = ⓑ{a,I} V2. U2.
#a #I #T2 #cs elim cs -cs
[ #V1 #U1 #H
  <(lifts_inv_nil … H) -H /2 width=5 by ex3_2_intro, lifts_nil/
| #l #m #cs #IHcs #V1 #U1 #H
  elim (lifts_inv_cons … H) -H #X #H #HT2
  elim (lift_inv_bind1 … H) -H #V #U #HV1 #HU1 #H destruct
  elim (IHcs … HT2) -IHcs -HT2 #V2 #U2 #HV2 #HU2 #H destruct
  /3 width=5 by ex3_2_intro, lifts_cons/
]
qed-.

lemma lifts_inv_flat1: ∀I,T2,cs,V1,U1. ⬆*[cs] ⓕ{I} V1. U1 ≡ T2 →
                       ∃∃V2,U2. ⬆*[cs] V1 ≡ V2 & ⬆*[cs] U1 ≡ U2 &
                                T2 = ⓕ{I} V2. U2.
#I #T2 #cs elim cs -cs
[ #V1 #U1 #H
  <(lifts_inv_nil … H) -H /2 width=5 by ex3_2_intro, lifts_nil/
| #l #m #cs #IHcs #V1 #U1 #H
  elim (lifts_inv_cons … H) -H #X #H #HT2
  elim (lift_inv_flat1 … H) -H #V #U #HV1 #HU1 #H destruct
  elim (IHcs … HT2) -IHcs -HT2 #V2 #U2 #HV2 #HU2 #H destruct
  /3 width=5 by ex3_2_intro, lifts_cons/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lifts_simple_dx: ∀T1,T2,cs. ⬆*[cs] T1 ≡ T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄.
#T1 #T2 #cs #H elim H -T1 -T2 -cs /3 width=5 by lift_simple_dx/
qed-.

lemma lifts_simple_sn: ∀T1,T2,cs. ⬆*[cs] T1 ≡ T2 → 𝐒⦃T2⦄ → 𝐒⦃T1⦄.
#T1 #T2 #cs #H elim H -T1 -T2 -cs /3 width=5 by lift_simple_sn/
qed-.

(* Basic properties *********************************************************)

lemma lifts_bind: ∀a,I,T2,V1,V2,cs. ⬆*[cs] V1 ≡ V2 →
                  ∀T1. ⬆*[cs + 1] T1 ≡ T2 →
                  ⬆*[cs] ⓑ{a,I} V1. T1 ≡ ⓑ{a,I} V2. T2.
#a #I #T2 #V1 #V2 #cs #H elim H -V1 -V2 -cs
[ #V #T1 #H >(lifts_inv_nil … H) -H //
| #V1 #V #V2 #cs #l #m #HV1 #_ #IHV #T1 #H
  elim (lifts_inv_cons … H) -H /3 width=3 by lift_bind, lifts_cons/
]
qed.

lemma lifts_flat: ∀I,T2,V1,V2,cs. ⬆*[cs] V1 ≡ V2 →
                  ∀T1. ⬆*[cs] T1 ≡ T2 →
                  ⬆*[cs] ⓕ{I} V1. T1 ≡ ⓕ{I} V2. T2.
#I #T2 #V1 #V2 #cs #H elim H -V1 -V2 -cs
[ #V #T1 #H >(lifts_inv_nil … H) -H //
| #V1 #V #V2 #cs #l #m #HV1 #_ #IHV #T1 #H
  elim (lifts_inv_cons … H) -H /3 width=3 by lift_flat, lifts_cons/
]
qed.

lemma lifts_total: ∀cs,T1. ∃T2. ⬆*[cs] T1 ≡ T2.
#cs elim cs -cs /2 width=2 by lifts_nil, ex_intro/
#l #m #cs #IH #T1 elim (lift_total T1 l m)
#T #HT1 elim (IH T) -IH /3 width=4 by lifts_cons, ex_intro/
qed.
