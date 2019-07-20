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

include "static_2/notation/relations/suptermopt_6.ma".
include "static_2/notation/relations/suptermopt_7.ma".
include "static_2/s_transition/fqu.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* Basic_2A1: was: fquqa *)
(* Basic_2A1: includes: fquq_inv_gen *)
definition fquq: bool → tri_relation genv lenv term ≝
                 λb. tri_RC … (fqu b).

interpretation
   "extended optional structural successor (closure)"
   'SupTermOpt b G1 L1 T1 G2 L2 T2 = (fquq b G1 L1 T1 G2 L2 T2).

interpretation
   "optional structural successor (closure)"
   'SupTermOpt G1 L1 T1 G2 L2 T2 = (fquq true G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

(* Basic_2A1: includes: fquqa_refl *)
lemma fquq_refl: ∀b. tri_reflexive … (fquq b).
// qed.

lemma fqu_fquq: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ ⬂⸮[b] ⦃G2,L2,T2⦄.
/2 width=1 by or_introl/ qed.

(* Basic_2A1: removed theorems 8:
              fquq_lref_O fquq_pair_sn fquq_bind_dx fquq_flat_dx fquq_drop
              fquqa_drop fquq_fquqa fquqa_inv_fquq
*)
