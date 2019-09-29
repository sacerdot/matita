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

include "static_2/relocation/drops.ma".
include "basic_2/rt_computation/jsx.ma".

(* COMPATIBILITY OF STRONG NORMALIZATION FOR UNBOUND RT-TRANSITION **********)

(* Forward lemmas with uniform slicing for local environments ***************)

lemma jsx_fwd_drops_atom_sn (h) (b) (G):
      ∀L1,L2. G ⊢ L1 ⊒[h] L2 →
      ∀f. 𝐔⦃f⦄ → ⇩*[b,f]L1 ≘ ⋆ → ⇩*[b,f]L2 ≘ ⋆.
#h #b #G #L1 #L2 #H elim H -L1 -L2
[ #f #_ #H //
| #I #K1 #K2 #_ #IH #f #Hf #H
| #I #K1 #K2 #V #_ #HV #IH #f #Hf #H
]
elim (drops_inv_bind1_isuni … H) -H [3,6: // |*: * -Hf ]
[1,3: #_ #H destruct
|2,4: #g #Hg #HK1 #H destruct /3 width=1 by drops_drop/
]
qed-.

lemma jsx_fwd_drops_unit_sn (h) (b) (G):
      ∀L1,L2. G ⊢ L1 ⊒[h] L2 →
      ∀f. 𝐔⦃f⦄ → ∀I,K1. ⇩*[b,f]L1 ≘ K1.ⓤ{I} →
      ∃∃K2. G ⊢ K1 ⊒[h] K2 & ⇩*[b,f]L2 ≘ K2.ⓤ{I}.
#h #b #G #L1 #L2 #H elim H -L1 -L2
[ #f #_ #J #Y1 #H
  lapply (drops_inv_atom1 … H) -H * #H #_ destruct
| #I #K1 #K2 #HK12 #IH #f #Hf #J #Y1 #H
| #I #K1 #K2 #V #HK12 #HV #IH #f #Hf #J #Y1 #H
]
elim (drops_inv_bind1_isuni … H) -H [3,6: // |*: * -Hf ]
[1,3: #Hf #H destruct -IH /3 width=3 by drops_refl, ex2_intro/
|2,4:
  #g #Hg #HK1 #H destruct
  elim (IH … Hg … HK1) -K1 -Hg #Y2 #HY12 #HKY2 
  /3 width=3 by drops_drop, ex2_intro/
]
qed-.

lemma jsx_fwd_drops_pair_sn (h) (b) (G):
      ∀L1,L2. G ⊢ L1 ⊒[h] L2 →
      ∀f. 𝐔⦃f⦄ → ∀I,K1,V. ⇩*[b,f]L1 ≘ K1.ⓑ{I}V →
      ∨∨ ∃∃K2. G ⊢ K1 ⊒[h] K2 & ⇩*[b,f]L2 ≘ K2.ⓑ{I}V
       | ∃∃K2. G ⊢ K1 ⊒[h] K2 & ⇩*[b,f]L2 ≘ K2.ⓧ & G ⊢ ⬈*[h,V] 𝐒⦃K2⦄.
#h #b #G #L1 #L2 #H elim H -L1 -L2
[ #f #_ #J #Y1 #X1 #H
  lapply (drops_inv_atom1 … H) -H * #H #_ destruct
| #I #K1 #K2 #HK12 #IH #f #Hf #J #Y1 #X1 #H
| #I #K1 #K2 #V #HK12 #HV #IH #f #Hf #J #Y1 #X1 #H
]
elim (drops_inv_bind1_isuni … H) -H [3,6: // |*: * -Hf ]
[1,3:
  #Hf #H destruct -IH
  /4 width=4 by drops_refl, ex3_intro, ex2_intro, or_introl, or_intror/
|2,4:
  #g #Hg #HK1 #H destruct
  elim (IH … Hg … HK1) -K1 -Hg * #Y2 #HY12 #HKY2 [2,4: #HX1 ]
  /4 width=4 by drops_drop, ex3_intro, ex2_intro, or_introl, or_intror/
]
qed-.
