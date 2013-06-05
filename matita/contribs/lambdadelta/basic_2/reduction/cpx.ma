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

include "basic_2/static/ssta.ma".
include "basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

inductive cpx (h) (g): lenv → relation term ≝
| cpx_cpr : ∀I,L,U2. L ⊢ ⓪{I} ➡ U2 → cpx h g L (⓪{I}) U2
| cpx_ssta: ∀I,L,U2,l. ⦃h, L⦄ ⊢ ⓪{I} •[g] ⦃l+1, U2⦄ → cpx h g L (⓪{I}) U2
| cpx_bind: ∀a,I,L,V1,V2,T1,T2,U2. cpx h g L V1 V2 → cpx h g (L.ⓑ{I}V1) T1 T2 →
            L ⊢ ⓑ{a,I}V2.T2 ➡ U2 → cpx h g L (ⓑ{a,I}V1.T1) U2
| cpx_flat: ∀I,L,V1,V2,T1,T2,U2. cpx h g L V1 V2 → cpx h g L T1 T2 →
            L ⊢ ⓕ{I}V2.T2 ➡ U2 → cpx h g L (ⓕ{I}V1.T1) U2
.

interpretation
   "context-sensitive extended parallel reduction (term)"
   'PRed h g L T1 T2 = (cpx h g L T1 T2).

(* Basic properties *********************************************************)

(* Note: this is "∀h,g,L. reflexive … (cpx h g L)" *)
lemma cpx_refl: ∀h,g,T,L. ⦃h, L⦄ ⊢ T ➡[g] T.
#h #g #T elim T -T /2 width=1/ * /2 width=5/
qed.

lemma cpr_cpx: ∀h,g,T1,L,T2. L ⊢ T1 ➡ T2 → ⦃h, L⦄ ⊢ T1 ➡[g] T2.
#h #g #T1 elim T1 -T1 /2 width=1/ * /2 width=5/
qed.

lemma ssta_cpx: ∀h,g,T1,L,T2,l. ⦃h, L⦄ ⊢ T1 •[g] ⦃l+1, T2⦄ → ⦃h, L⦄ ⊢ T1 ➡[g] T2.
#h #g #T1 elim T1 -T1 /2 width=2/ * [|*]
[ #a #I #V1 #T1 #_ #IHT1 #L #X #l #H
  elim (ssta_inv_bind1 … H) -H #T2 #HT12 #H destruct /3 width=5/
| #V1 #T1 #_ #IHT1 #L #X #l #H
  elim (ssta_inv_appl1 … H) -H #T2 #HT12 #H destruct /3 width=5/
| #V1 #T1 #_ #IHT1 #L #X #l #H
  lapply (ssta_inv_cast1 … H) -H /3 width=5/
]
qed.
