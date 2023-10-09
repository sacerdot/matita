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

include "ground/relocation/fu/fur_height.ma".
include "ground/relocation/fu/fur_dapp_lt.ma".
include "ground/arith/nat_rminus.ma".
include "ground/arith/nat_plus_rplus.ma".

(* LENGTH FOR FINITE RELOCATION MAPS FOR UNWIND ************)

definition fur_length: relation2 (𝔽𝕌) (ℕ⁺) ≝
           λf,q. ∧∧ ∀p. q ≤ p → f＠⧣❨p❩ = p+♯f
                  & ∀p. p < q → f＠⧣❨p❩ < p+♯f
.

(* Basic constructions ******************************************************)

lemma pippo (A:Type[0]) (Q:predicate …) (a:A):
      (∀b. b = a → Q b) → Q a.
#A #Q #a #H0 @H0 //
qed.
(*
lemma fur_length_total (f):
      ∃q. fur_length f q.
#f elim f -f
[| * [| #k ] #f * #q * #H1q #H2q ]
[ @(ex_intro … (𝟏)) @conj #p #H0
  [ //
  | elim (plt_inv_unit_dx … H0)
  ]
| @(pippo … (♯f))
  * [| #n ] #Hn
  <Hn in H2q; <Hn in H1q; #H1q #H2q
  [ @(ex_intro … (q)) @conj <fur_height_p_dx <Hn -Hn
    [ * [| #p ] #H0 //
      elim (ple_split_lt_eq … H0) -H0 #H0 destruct
      [ <fur_dapp_p_dx_succ >H1q
        /2 width=1 by plt_inv_succ_dx/
      | lapply (H2q p ?) // #H0
        elim (plt_ge_false … H0) //
      ]
    | #p #H0
      lapply (H2q … H0) -H0 #H0
      elim (plt_ge_false … H0) //
    ]
  | @(ex_intro … (↑q)) @conj <fur_height_p_dx <Hn -Hn
    [ * [| #p ] #H0
      [ elim (plt_inv_unit_dx … H0)
      | <fur_dapp_p_dx_succ
        >H1q /2 width=1 by ple_inv_succ_bi/
      ]
    | * [| #p ] #H0 //
      <fur_dapp_p_dx_succ <nrplus_succ_sn
      /4 width=1 by plt_inv_succ_bi, plt_succ_bi/
    ]
  ]
| @(ex_intro … (q-k)) @conj #p #H0 <fur_dapp_j_dx <fur_height_j_dx
  [ >H1q //
  | elim (pnat_split_lt_ge (↑k) q) #Hk
    [ lapply (H2q (p+k) ?) //
    |
  ]
]

include "ground/relocation/fu/fur_eq.ma".

lemma pippo (q) (f1) (f2):
            f1 ≐ f2 →
            fur_length f1 q → fur_length f2 q.
#q #f1 #f2 #Hf * #H1ge #H1lt
@conj #p #Hp         

(f1) (f2) (q) :
      
      
*)