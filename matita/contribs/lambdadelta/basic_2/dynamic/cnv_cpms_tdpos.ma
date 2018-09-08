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

include "basic_2/dynamic/cnv_cpm_tdpos.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Forward lemmas with positive rt-computation for terms ********************)

lemma cpms_fwd_tdpos_sn (a) (h) (o) (n) (G) (L):
                        ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] → 𝐏[h,o]⦃T1⦄ →
                        ∀T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 →
                        ∨∨ ∧∧ T1 = T2 & 0 = n
                         | ∃∃n1,n2,T. ⦃G,L⦄ ⊢ T1 ➡[n1,h] T & (T1 ≛[h,o] T → ⊥) & ⦃G,L⦄ ⊢ T ➡*[n2,h] T2 & n1+n2=n.
#a #h #o #n #G #L #T1 #H1T1 #H2T1 #T2 #H
@(cpms_ind_dx … H) -n -T2
[ /3 width=1 by or_introl, conj/
| #n1 #n2 #T #T2 #HT1 * *
  [ #H1 #H2 #HT2 destruct -HT1
    elim (cpm_fwd_tdpos_sn … H1T1 H2T1 … HT2) -H1T1 -H2T1
    [ * #H1 #H2 destruct -HT2 /3 width=1 by or_introl, conj/
    | #HnT2 >commutative_plus in ⊢ (??%); /4 width=7 by ex4_3_intro, or_intror/
    ]
  | #m1 #m2 #T0 #H1T10 #H2T10 #HT0 #H #HT2 destruct -H1T1 -H2T1 -HT1
    >associative_plus in ⊢ (??%); /4 width=7 by cpms_step_dx, ex4_3_intro, or_intror/
  ]
]
qed-.
