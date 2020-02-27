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

include "ground/relocation/rtmap_after.ma".
include "ground/relocation/rtmap_basic.ma".

(* RELOCATION MAP ***********************************************************)

(* Properties with composition **********************************************)

lemma after_basic_rc (m2,m1,n2,n1):
                     m1 ≤ m2 → m2 ≤ m1+n1 → 𝐁❨m2,n2❩ ⊚ 𝐁❨m1,n1❩ ≘ 𝐁❨m1,n2+n1❩.
#m2 elim m2 -m2
[ #m1 #n2 #n1 #Hm21 #_
  <(le_n_O_to_eq … Hm21) -m1 //
| #m2 #IH *
  [ #n2 #n1 #_ < plus_O_n #H
    elim (le_inv_S1 … H) -H #x #Hx #H destruct
    <plus_n_Sm
    @after_push [4:|*: // ]
    @(IH 0 … Hx) -IH -n2 -x //
  | #m1 #n2 #n1 #H1 #H2
    lapply (le_S_S_to_le … H1) -H1 #H1
    lapply (le_S_S_to_le … H2) -H2 #H2
    /3 width=7 by after_refl/
  ]
]
qed.
