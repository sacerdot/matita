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

include "ground_2/lib/arith.ma".

(* SORT HIERARCHY ***********************************************************)

(* sort hierarchy specification *)
record sh: Type[0] ≝ {
   next   : nat → nat;     (* next sort in the hierarchy *)
   next_lt: ∀k. k < next k (* strict monotonicity condition *)
}.

definition sh_N: sh ≝ mk_sh S ….
// defined.

(* Basic properties *********************************************************)

lemma nexts_le: ∀h,k,d. k ≤ (next h)^d k.
#h #k #d elim d -d // normalize #d #IHd
lapply (next_lt h ((next h)^d k)) #H
lapply (le_to_lt_to_lt … IHd H) -IHd -H /2 width=2 by lt_to_le/
qed.

lemma nexts_lt: ∀h,k,d. k < (next h)^(d+1) k.
#h #k #d >iter_SO
lapply (nexts_le h k d) #H
@(le_to_lt_to_lt … H) //
qed.

axiom nexts_dec: ∀h,k1,k2. Decidable (∃d. (next h)^d k1 = k2).

axiom nexts_inj: ∀h,k,d1,d2. (next h)^d1 k = (next h)^d2 k → d1 = d2.
