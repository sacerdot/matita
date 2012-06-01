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

include "basic_2/reducibility/cpr.ma".
include "basic_2/reducibility/cnf.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

definition csn: lenv → predicate term ≝ λL. SN … (cpr L) (eq …).

interpretation
   "context-sensitive strong normalization (term)"
   'SN L T = (csn L T).

(* Basic eliminators ********************************************************)

lemma csn_ind: ∀L. ∀R:predicate term.
               (∀T1. L ⊢ ⬇* T1 →
                     (∀T2. L ⊢ T1 ➡ T2 → (T1 = T2 → ⊥) → R T2) →
                     R T1
               ) →
               ∀T. L ⊢ ⬇* T → R T.
#L #R #H0 #T1 #H elim H -T1 #T1 #HT1 #IHT1
@H0 -H0 /3 width=1/ -IHT1 /4 width=1/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: sn3_pr2_intro *)
lemma csn_intro: ∀L,T1.
                 (∀T2. L ⊢ T1 ➡ T2 → (T1 = T2 → ⊥) → L ⊢ ⬇* T2) → L ⊢ ⬇* T1.
/4 width=1/ qed.

(* Basic_1: was: sn3_nf2 *)
lemma csn_cnf: ∀L,T. L ⊢ 𝐍⦃T⦄ → L ⊢ ⬇* T.
/2 width=1/ qed.

lemma csn_cpr_trans: ∀L,T1. L ⊢ ⬇* T1 → ∀T2. L ⊢ T1 ➡ T2 → L ⊢ ⬇* T2.
#L #T1 #H elim H -T1 #T1 #HT1 #IHT1 #T2 #HLT12
@csn_intro #T #HLT2 #HT2
elim (term_eq_dec T1 T2) #HT12
[ -IHT1 -HLT12 destruct /3 width=1/
| -HT1 -HT2 /3 width=4/
qed.

(* Basic_1: was: sn3_cast *)
lemma csn_cast: ∀L,W. L ⊢ ⬇* W → ∀T. L ⊢ ⬇* T → L ⊢ ⬇* ⓝW. T.
#L #W #HW elim HW -W #W #_ #IHW #T #HT @(csn_ind … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpr_inv_cast1 … H1) -H1
[ * #W0 #T0 #HLW0 #HLT0 #H destruct
  elim (eq_false_inv_tpair_sn … H2) -H2
  [ /3 width=3/
  | -HLW0 * #H destruct /3 width=1/ 
  ]
| /3 width=3/
]
qed.

(* Basic forward lemmas *****************************************************)

fact csn_fwd_flat_dx_aux: ∀L,U. L ⊢ ⬇* U → ∀I,V,T. U = ⓕ{I} V. T → L ⊢ ⬇* T.
#L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csn_intro #T2 #HLT2 #HT2
@(IH (ⓕ{I} V. T2)) -IH // /2 width=1/ -HLT2 #H destruct /2 width=1/
qed.

(* Basic_1: was: sn3_gen_flat *)
lemma csn_fwd_flat_dx: ∀I,L,V,T. L ⊢ ⬇* ⓕ{I} V. T → L ⊢ ⬇* T.
/2 width=5/ qed-.

(* Basic_1: removed theorems 14:
            sn3_cdelta
            sn3_gen_cflat sn3_cflat sn3_cpr3_trans sn3_shift sn3_change
            sn3_appl_cast sn3_appl_beta sn3_appl_lref sn3_appl_abbr
            sn3_appl_appls sn3_bind sn3_appl_bind sn3_appls_bind
*)
