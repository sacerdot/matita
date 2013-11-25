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
// qed.

(* Basic properties *********************************************************)

lemma nexts_le: ∀h,k,l. k ≤ (next h)^l k.
#h #k #l elim l -l // normalize #l #IHl
lapply (next_lt h ((next h)^l k)) #H
lapply (le_to_lt_to_lt … IHl H) -IHl -H /2 width=2/
qed.

lemma nexts_lt: ∀h,k,l. k < (next h)^(l+1) k.
#h #k #l >iter_SO
lapply (nexts_le h k l) #H
@(le_to_lt_to_lt … H) //
qed.

axiom nexts_dec: ∀h,k1,k2. Decidable (∃l. (next h)^l k1 = k2).

axiom nexts_inj: ∀h,k,l1,l2. (next h)^l1 k = (next h)^l2 k → l1 = l2.
