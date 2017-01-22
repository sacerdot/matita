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
   next_lt: ∀s. s < next s (* strict monotonicity condition *)
}.

definition sh_N: sh ≝ mk_sh S ….
// defined.

(* Basic properties *********************************************************)

lemma nexts_le: ∀h,s,n. s ≤ (next h)^n s.
#h #s #n elim n -n // normalize #n #IH
lapply (next_lt h ((next h)^n s)) #H
lapply (le_to_lt_to_lt … IH H) -IH -H /2 width=2 by lt_to_le/
qed.

lemma nexts_lt: ∀h,s,n. s < (next h)^(⫯n) s.
#h #s #n normalize
lapply (nexts_le h s n) #H
@(le_to_lt_to_lt … H) //
qed.

axiom nexts_dec: ∀h,s1,s2. Decidable (∃n. (next h)^n s1 = s2).

axiom nexts_inj: ∀h,s,n1,n2. (next h)^n1 s = (next h)^n2 s → n1 = n2.
