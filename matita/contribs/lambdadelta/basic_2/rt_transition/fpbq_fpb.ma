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

include "static_2/static/feqg_fqup.ma".
include "static_2/static/feqg_feqg.ma".
include "basic_2/rt_transition/fpb_feqg.ma".
include "basic_2/rt_transition/fpbq.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Properties with proper parallel rst-transition for closures **************)

lemma fpb_fpbq:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ →
      ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=1 by fpbq_fquq, fpbq_cpx, fpbq_lpx, fqu_fquq/
qed.

(* Basic_2A1: fpb_fpbq_alt *)
lemma fpb_fpbq_fneqx (S):
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ →
      ∧∧ ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ & (❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → ⊥).
/3 width=10 by fpb_fpbq, fpb_inv_feqg, conj/ qed-.

(* Inversrion lemmas with proper parallel rst-transition for closures *******)

(* Basic_2A1: fpbq_inv_fpb_alt *)
lemma fpbq_fneqx_inv_fpb:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ →
      (❪G1,L1,T1❫ ≅ ❪G2,L2,T2❫ → ⊥) → ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 * [2: * #H1 #H2 #H3 destruct ]
  [ #H elim H -H /2 width=1 by feqg_refl/
  | /2 width=1 by fpb_fqu/
  ]
| /4 width=1 by fpb_cpx, teqg_feqg/
| /4 width=1 by fpb_lpx, feqg_intro_sn/
| #G2 #L2 #T2 #H12 #Hn12
  elim Hn12 -Hn12 //
]
qed-.

(* Basic_2A1: uses: fpbq_ind_alt *)
lemma fpbq_inv_fpb:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ →
      ∨∨ ❪G1,L1,T1❫ ≅ ❪G2,L2,T2❫
       | ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T2 #H 
elim (feqg_dec sfull … G1 G2 L1 L2 T1 T2) //
[ /2 width=1 by or_introl/
| /4 width=1 by fpbq_fneqx_inv_fpb, or_intror/
]
qed-.
