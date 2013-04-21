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

lemma arith1: ∀x,y,z,w. z < y → x + (y + w) - z = x + y - z + w.
#x #y #z #w #H <le_plus_minus_comm // /3 width=1 by lt_to_le, le_plus_a/
qed-.

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

notation "hvbox( ⦃term 46 h, break term 46 L⦄ ⊢ break term 46 T1 ➡ break [ term 46 g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'XPRed $h $g $L $T1 $T2 }.

inductive xpr (h) (g): lenv → relation term ≝
| xpr_cpr : ∀I,L,U2. L ⊢ ⓪{I} ➡ U2 → xpr h g L (⓪{I}) U2
| xpr_ssta: ∀I,L,U2,l. ⦃h, L⦄ ⊢ ⓪{I} •[g] ⦃l+1, U2⦄ → xpr h g L (⓪{I}) U2
| xpr_bind: ∀a,I,L,V1,V2,T1,T2,U2. xpr h g L V1 V2 → xpr h g (L.ⓑ{I}V1) T1 T2 →
            L ⊢ ⓑ{a,I}V2.T2 ➡ U2 → xpr h g L (ⓑ{a,I}V1.T1) U2
| xpr_flat: ∀I,L,V1,V2,T1,T2,U2. xpr h g L V1 V2 → xpr h g L T1 T2 →
            L ⊢ ⓕ{I}V2.T2 ➡ U2 → xpr h g L (ⓕ{I}V1.T1) U2
.

interpretation
   "context-sensitive extended parallel reduction (term)"
   'XPRed h g L T1 T2 = (xpr h g L T1 T2).

(* Basic properties *********************************************************)

(* Note: this is "∀h,g,L. reflexive … (xpr h g L)" *)
lemma xpr_refl: ∀h,g,T,L. ⦃h, L⦄ ⊢ T ➡[g] T.
#h #g #T elim T -T /2 width=1/ * /2 width=5/
qed.

lemma cpr_xpr: ∀h,g,T1,L,T2. L ⊢ T1 ➡ T2 → ⦃h, L⦄ ⊢ T1 ➡[g] T2.
#h #g #T1 elim T1 -T1 /2 width=1/ * /2 width=5/
qed.

lemma ssta_xpr: ∀h,g,T1,L,T2,l. ⦃h, L⦄ ⊢ T1 •[g] ⦃l+1, T2⦄ → ⦃h, L⦄ ⊢ T1 ➡[g] T2.
#h #g #T1 elim T1 -T1 /2 width=2/ * [|*]
[ #a #I #V1 #T1 #_ #IHT1 #L #X #l #H
  elim (ssta_inv_bind1 … H) -H #T2 #HT12 #H destruct /3 width=5/
| #V1 #T1 #_ #IHT1 #L #X #l #H
  elim (ssta_inv_appl1 … H) -H #T2 #HT12 #H destruct /3 width=5/
| #V1 #T1 #_ #IHT1 #L #X #l #H
  lapply (ssta_inv_cast1 … H) -H /3 width=5/
]
qed.

include "basic_2/relocation/lift_lift.ma".
include "basic_2/relocation/fsup.ma".
include "basic_2/substitution/lpss_ldrop.ma".

