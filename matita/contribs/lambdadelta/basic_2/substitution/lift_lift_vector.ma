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

include "basic_2/substitution/lift_lift.ma".
include "basic_2/substitution/lift_vector.ma".

(* BASIC TERM VECTOR RELOCATION *********************************************)

(* Main properties ***********************************************************)

theorem liftv_mono: ∀Ts,U1s,d,e. ⇧[d,e] Ts ≡ U1s →
                    ∀U2s:list term. ⇧[d,e] Ts ≡ U2s → U1s = U2s.
#Ts #U1s #d #e #H elim H -Ts -U1s
[ #U2s #H >(liftv_inv_nil1 … H) -H //
| #Ts #U1s #T #U1 #HTU1 #_ #IHTU1s #X #H destruct
  elim (liftv_inv_cons1 … H) -H #U2 #U2s #HTU2 #HTU2s #H destruct
  >(lift_mono … HTU1 … HTU2) -T /3 width=1/
]
qed.
