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
include "basic_2/rt_transition/fpbc.ma".

(* STRONGLY NORMALIZING CLOSURES FOR PARALLEL RST-TRANSITION ****************)

definition fsb: relation3 genv lenv term ≝
           SN3 … fpb (feqg sfull).

interpretation
  "strong normalization for parallel rst-transition (closure)"
  'PRedSubTyStrong G L T = (fsb G L T).

(* Basic properties *********************************************************)

lemma fsb_intro (G1) (L1) (T1):
      (∀G2,L2,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ → ≥𝐒 ❪G2,L2,T2❫) → ≥𝐒 ❪G1,L1,T1❫.
/5 width=1 by fpbc_intro, SN3_intro/ qed.

(* Basic eliminators ********************************************************)

(* Note: eliminator with shorter ground hypothesis *)
lemma fsb_ind (Q:relation3 …):
      (∀G1,L1,T1. ≥𝐒 ❪G1,L1,T1❫ →
        (∀G2,L2,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ → Q G2 L2 T2) →
        Q G1 L1 T1
      ) →
      ∀G,L,T. ≥𝐒 ❪G,L,T❫ → Q G L T.
#Q #IH #G #L #T #H elim H -G -L -T
#G1 #L1 #T1 #H1 #IH1
@IH -IH [ /4 width=1 by SN3_intro/ ] -H1 #G2 #L2 #T2 #H
elim (fpbc_inv_gen sfull … H) -H #H12 #Hn12 /3 width=1 by/
qed-.

(* Basic_2A1: removed theorems 6:
              fsba_intro fsba_ind_alt fsba_fpbs_trans fsb_fsba fsba_inv_fsb
              aaa_fsba
*)
