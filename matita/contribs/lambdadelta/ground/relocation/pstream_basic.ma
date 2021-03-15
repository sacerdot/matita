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

include "ground/arith/nat_lt_plus.ma".
include "ground/relocation/rtmap_basic_at.ma".
include "ground/relocation/pstream_after.ma".

(* RELOCATION N-STREAM ******************************************************)

(* Specific properties on basic relocation **********************************)

lemma apply_basic_lt: ∀m,n,i. ninj i ≤ m → 𝐁❨m,n❩@❨i❩ = i.
/3 width=1 by at_inv_total, at_basic_lt/ qed-.

lemma apply_basic_ge: ∀m,n,i. m < ninj i → 𝐁❨m,n❩@❨i❩ = i+n.
/3 width=1 by at_inv_total, at_basic_ge/ qed-.

(* Specific main properties on basic relocation *****************************)

theorem basic_swap: ∀d1,d2. d2 ≤ d1 →
                    ∀h1,h2. 𝐁❨d2,h2❩∘𝐁❨d1,h1❩ ≡ 𝐁❨d1+h2,h1❩∘𝐁❨d2,h2❩.
#d1 #d2 #Hd21 #h1 #h2
@nstream_inv_eq
@nstream_eq_inv_ext #i
<compose_apply <compose_apply
elim (nat_split_lt_ge d2 i) #Hd2
[ elim (nat_split_lt_ge d1 i) -Hd21 #Hd1
  [ >(apply_basic_ge … Hd1) >(apply_basic_ge … Hd2) >apply_basic_ge
    [ >apply_basic_ge // >nrplus_inj_sn /2 width=1 by nlt_plus_bi_sn/
    | >nrplus_inj_sn /2 width=2 by nlt_plus_dx_dx/
    ]
  | >(apply_basic_lt … Hd1) >(apply_basic_ge … Hd2)
    >apply_basic_lt // >nrplus_inj_sn /2 width=1 by nle_plus_bi_dx/
  ]
| lapply (nle_trans … Hd2 … Hd21) -Hd21 #Hd1
  >(apply_basic_lt … Hd1) >(apply_basic_lt … Hd2)
  >apply_basic_lt /2 width=1 by nle_plus_dx_dx/
]
qed-.
