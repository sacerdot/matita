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

include "ground_2/xoa/ex_4_4.ma".
include "ground_2/relocation/rtmap_id.ma".
include "static_2/notation/relations/subseteq_4.ma".
include "static_2/syntax/lveq.ma".
include "static_2/static/frees.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

definition fsle: bi_relation lenv term ≝ λL1,T1,L2,T2.
                 ∃∃n1,n2,f1,f2. L1 ⊢ 𝐅+❪T1❫ ≘ f1 & L2 ⊢ 𝐅+❪T2❫ ≘ f2 &
                                L1 ≋ⓧ*[n1,n2] L2 & ⫱*[n1]f1 ⊆ ⫱*[n2]f2.

interpretation "free variables inclusion (restricted closure)"
   'SubSetEq L1 T1 L2 T2 = (fsle L1 T1 L2 T2).

interpretation "free variables inclusion (term)"
   'subseteq T1 T2 = (fsle LAtom T1 LAtom T2).

(* Basic properties *********************************************************)

lemma fsle_sort: ∀L,s1,s2. ❪L,⋆s1❫ ⊆ ❪L,⋆s2❫.
/3 width=8 by frees_sort, sle_refl, ex4_4_intro/ qed.

lemma fsle_gref: ∀L,l1,l2. ❪L,§l1❫ ⊆ ❪L,§l2❫.
/3 width=8 by frees_gref, sle_refl, ex4_4_intro/ qed.
