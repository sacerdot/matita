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

include "ground/relocation/rtmap_basic.ma".
include "ground/relocation/nstream_after.ma".

(* RELOCATION N-STREAM ******************************************************)

(* Specific properties on basic relocation **********************************)

lemma apply_basic_lt: ∀m,n,i. i < m → 𝐁❨m,n❩@❨i❩ = i.
/3 width=1 by at_inv_total, at_basic_lt/ qed-.

lemma apply_basic_ge: ∀m,n,i. m ≤ i → 𝐁❨m,n❩@❨i❩ = n+i.
/3 width=1 by at_inv_total, at_basic_ge/ qed-.

(* Specific main properties on basic relocation *****************************)

theorem basic_swap: ∀d1,d2. d2 ≤ d1 →
                    ∀h1,h2. 𝐁❨d2,h2❩∘𝐁❨d1,h1❩ ≡ 𝐁❨h2+d1,h1❩∘𝐁❨d2,h2❩.
#d1 #d2 #Hd21 #h1 #h2
@nstream_inv_eq
@nstream_eq_inv_ext #i
<compose_apply <compose_apply
elim (lt_or_ge i d2) #Hd2
[ lapply (lt_to_le_to_lt … Hd2 Hd21) -Hd21 #Hd1
  >(apply_basic_lt … Hd1) >(apply_basic_lt … Hd2) >apply_basic_lt
  /2 width=1 by le_plus_a/
| elim (lt_or_ge i d1) -Hd21 #Hd1
  [ >(apply_basic_lt … Hd1) >(apply_basic_ge … Hd2) >apply_basic_lt
    /2 width=1 by monotonic_lt_plus_r/
  | >(apply_basic_ge … Hd1) >(apply_basic_ge … Hd2)
    >apply_basic_ge [2: /2 width=1 by le_plus_a/ ]
    >apply_basic_ge /2 width=1 by monotonic_le_plus_r/
  ]
]
qed-.
