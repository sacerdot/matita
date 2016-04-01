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
include "basic_2/static/lsubr.ma".

(* RESTRICTED REFINEMENT FOR LOCAL ENVIRONMENTS *****************************)

(* Forward lemmas with generic slicing for local environments ***************)

(* Basic_2A1: includes: lsubr_fwd_drop2_pair *)
lemma lsubr_fwd_drops2_pair: ∀L1,L2. L1 ⫃ L2 → 
                             ∀I,K2,W,c,f. 𝐔⦃f⦄ → ⬇*[c, f] L2 ≡ K2.ⓑ{I}W →
                             (∃∃K1. K1 ⫃ K2 & ⬇*[c, f] L1 ≡ K1.ⓑ{I}W) ∨
                             ∃∃K1,V. K1 ⫃ K2 & ⬇*[c, f] L1 ≡ K1.ⓓⓝW.V & I = Abst.
#L1 #L2 #H elim H -L1 -L2
[ #L #I #K2 #W #c #f #_ #H
  elim (drops_inv_atom1 … H) -H #H destruct
| #J #L1 #L2 #V #HL12 #IHL12 #I #K2 #W #c #f #Hf #H
  elim (drops_inv_pair1_isuni … Hf H) -H * #g #HLK2 try #H destruct [ -IHL12 | -HL12 ]
  [ /4 width=4 by drops_refl, ex2_intro, or_introl/
  | elim (IHL12 … HLK2) -IHL12 -HLK2 /2 width=3 by isuni_inv_next/ *
    /4 width=4 by drops_drop, ex3_2_intro, ex2_intro, or_introl, or_intror/
  ]
| #L1 #L2 #V1 #V2 #HL12 #IHL12 #I #K2 #W #c #f #Hf #H
  elim (drops_inv_pair1_isuni … Hf H) -H * #g #HLK2 try #H destruct [ -IHL12 | -HL12 ]
  [ /4 width=4 by drops_refl, ex3_2_intro, or_intror/
  | elim (IHL12 … HLK2) -IHL12 -HLK2 /2 width=3 by isuni_inv_next/ *
    /4 width=4 by drops_drop, ex3_2_intro, ex2_intro, or_introl, or_intror/
  ]
]
qed-.

(* Basic_2A1: includes: lsubr_fwd_drop2_abbr *)
lemma lsubr_fwd_drops2_abbr: ∀L1,L2. L1 ⫃ L2 →
                             ∀K2,V,c,f.  𝐔⦃f⦄ → ⬇*[c, f] L2 ≡ K2.ⓓV →
                             ∃∃K1. K1 ⫃ K2 & ⬇*[c, f] L1 ≡ K1.ⓓV.
#L1 #L2 #HL12 #K2 #V #c #f #Hf #HLK2
elim (lsubr_fwd_drops2_pair … HL12 … Hf HLK2) -L2 -Hf // *
#K1 #W #_ #_ #H destruct
qed-.
