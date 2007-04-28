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

set "baseuri" "cic:/matita/RELATIONAL/Zah/setoid".

include "NPlus/monoid.ma".
include "Zah/defs.ma".

theorem nplus_total: \forall p,q. \exists r. p + q == r.
 intros 2. elim q; clear q;
 decompose; auto.
qed.
(*
theorem zeq_intro: \forall z1,z2. 
                   (\forall n.((\fst z1) + (\snd z2) == n) \to ((\fst z2) + (\snd z1) == n)) \to
                   (\forall n.((\fst z2) + (\snd z1) == n) \to ((\fst z1) + (\snd z2) == n)) \to
                   z1 = z2.
 unfold ZEq. intros. apply iff_intro; intros; auto.
qed.

theorem zeq_refl: \forall z. z = z.
 unfold ZEq. intros. auto.
qed.

theorem zeq_sym: \forall z1,z2. z1 = z2 \to z2 = z1.
 unfold ZEq. intros. lapply linear (H n). auto.
qed.
*)(*
theorem zeq_trans: \forall z1,z2. z1 = z2 \to 
                   \forall z3. z2 = z3 \to z1 = z3.
 unfold ZEq. intros.
 lapply (nplus_total (\snd z2) (\fst z2)). decompose.
 
 
 
 apply iff_intro; intros;
 [ lapply (nplus_total (\fst z1) (\snd z3)). decompose
 |
 
 
 
 
 lapply (nplus_total (\snd z2) (\fst z2)). decompose.
 lapply (nplus_total n a). decompose.
 lapply linear (H a1). lapply linear (H1 a1). decompose.
 
 

*)
