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

include "basic_2/notation/relations/predsubtystrong_3.ma".
include "basic_2/rt_transition/fpb.ma".

(* STRONGLY NORMALIZING CLOSURES FOR PARALLEL RST-TRANSITION ****************)

inductive fsb: relation3 genv lenv term ≝
| fsb_intro: ∀G1,L1,T1.
             (∀G2,L2,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ → fsb G2 L2 T2) →
             fsb G1 L1 T1
.

interpretation
  "strong normalization for parallel rst-transition (closure)"
  'PRedSubTyStrong G L T = (fsb G L T).

(* Basic eliminators ********************************************************)

(* Note: eliminator with shorter ground hypothesis *)
(* Note: to be named fsb_ind when fsb becomes a definition like csx, rsx ****)
lemma fsb_ind_alt (Q:relation3 …):
      (∀G1,L1,T1. ≥𝐒 ❪G1,L1,T1❫ →
        (∀G2,L2,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ → Q G2 L2 T2) →
        Q G1 L1 T1
      ) →
      ∀G,L,T. ≥𝐒 ❪G,L,T❫ → Q G L T.
#Q #IH #G #L #T #H elim H -G -L -T
/4 width=1 by fsb_intro/
qed-.

(* Basic_2A1: removed theorems 6:
              fsba_intro fsba_ind_alt fsba_fpbs_trans fsb_fsba fsba_inv_fsb
              aaa_fsba
*)
