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

include "basic_2A/substitution/drop_drop.ma".
include "basic_2A/multiple/drops.ma".

(* ITERATED LOCAL ENVIRONMENT SLICING ***************************************)

(* Properties concerning basic local environment slicing ********************)

lemma drops_drop_trans: ∀L1,L,cs. ⬇*[Ⓕ, cs] L1 ≡ L → ∀L2,i. ⬇[i] L ≡ L2 →
                        ∃∃L0,cs0,i0. ⬇[i0] L1 ≡ L0 & ⬇*[Ⓕ, cs0] L0 ≡ L2 &
                                      @❪i, cs❫ ≘ i0 & cs ▭ i ≘ cs0.
#L1 #L #cs #H elim H -L1 -L -cs
[ /2 width=7 by drops_nil, minuss_nil, at_nil, ex4_3_intro/
| #L1 #L0 #L #cs #l #m #_ #HL0 #IHL0 #L2 #i #HL2
  elim (lt_or_ge i l) #Hil
  [ elim (drop_trans_le … HL0 … HL2) -L /2 width=2 by lt_to_le/
    #L #HL0 #HL2 elim (IHL0 … HL0) -L0 /3 width=7 by drops_cons, minuss_lt, at_lt, ex4_3_intro/
  | lapply (drop_trans_ge … HL0 … HL2 ?) -L // #HL02
    elim (IHL0 … HL02) -L0 /3 width=7 by minuss_ge, at_ge, ex4_3_intro/
  ]
]
qed-.
