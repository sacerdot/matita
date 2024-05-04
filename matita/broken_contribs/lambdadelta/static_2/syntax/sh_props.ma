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

include "static_2/syntax/sh_nexts.ma".

(* SORT HIERARCHY ***********************************************************)

(* acyclicity condition *)
record sh_acyclic (h): Prop ≝
{
(**) (* use extensional equivalence *)
  sh_nexts_inj: ∀s,n1,n2. ⇡*[h,n1]s = ⇡*[h,n2]s → n1 = n2
}.

(* decidability condition *)
record sh_decidable (h): Prop ≝
{
  sh_nexts_dec: ∀s1,s2. Decidable (∃n. ⇡*[h,n]s1 = s2)
}.
