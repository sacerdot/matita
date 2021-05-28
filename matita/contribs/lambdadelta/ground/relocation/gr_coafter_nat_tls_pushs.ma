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

include "ground/relocation/gr_pushs.ma".
include "ground/relocation/gr_tls.ma".
include "ground/relocation/gr_nat.ma".
include "ground/relocation/gr_coafter.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Forward lemmas with nat and iterated tail and pushs ************************************************)

(*** coafter_fwd_pushs *)
lemma gr_coafter_des_pushs_dx (n) (m):
      ∀g2,f1,g. g2 ~⊚ ⫯*[m]f1 ≘ g → @↑❪m, g2❫ ≘ n →
      ∃∃f. ⫱*[n]g2 ~⊚ f1 ≘ f & ⫯*[n] f = g.
#n @(nat_ind_succ … n) -n
[ #m #g2 #f1 #g #Hg #H
  elim (gr_nat_inv_zero_dx … H) -H [|*: // ] #f2 #H1 #H2 destruct
  /2 width=3 by ex2_intro/
| #n #IH * [| #m ] #g2 #f1 #g #Hg #H
  [ elim (gr_nat_inv_zero_succ … H) -H [|*: // ] #f2 #Hmn #H destruct
    elim (gr_coafter_inv_next_sn … Hg) -Hg [|*: // ] #f #Hf #H destruct
    elim (IH … Hf Hmn) -IH -Hf -Hmn /2 width=3 by ex2_intro/
  | elim (gr_nat_inv_succ_bi … H) -H [1,4: * |*: // ] #f2 #Hmn #H destruct
    [ elim (gr_coafter_inv_push_bi … Hg) -Hg [|*: // ] #f #Hf #H destruct
      elim (IH … Hf Hmn) -IH -Hf -Hmn /2 width=3 by ex2_intro/
    | elim (gr_coafter_inv_next_sn … Hg) -Hg [|*: // ] #f #Hf #H destruct
      elim (IH … Hf Hmn) -IH -Hf -Hmn /2 width=3 by ex2_intro/
    ]
  ]
]
qed-.
