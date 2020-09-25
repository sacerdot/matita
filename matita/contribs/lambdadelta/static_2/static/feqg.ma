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

include "static_2/notation/relations/stareqsn_7.ma".
include "static_2/syntax/genv.ma".
include "static_2/static/reqg.ma".

(* GENERIC EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *********************)

inductive feqg (S) (G) (L1) (T1): relation3 genv lenv term ≝
| feqg_intro_sn: ∀L2,T2. L1 ≛[S,T1] L2 → T1 ≛[S] T2 →
                 feqg S G L1 T1 G L2 T2
.

interpretation
  "generic equivalence on referred entries (closure)"
  'StarEqSn S G1 L1 T1 G2 L2 T2 = (feqg S G1 L1 T1 G2 L2 T2).

(* Basic_properties *********************************************************)

lemma feqg_intro_dx (S) (G):
      reflexive … S → symmetric … S →
      ∀L1,L2,T2. L1 ≛[S,T2] L2 →
      ∀T1. T1 ≛[S] T2 → ❪G,L1,T1❫ ≛[S] ❪G,L2,T2❫.
/3 width=6 by feqg_intro_sn, teqg_reqg_div/ qed.

(* Basic inversion lemmas ***************************************************)

lemma feqg_inv_gen_sn (S):
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ →
      ∧∧ G1 = G2 & L1 ≛[S,T1] L2 & T1 ≛[S] T2.
#S #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2 /2 width=1 by and3_intro/
qed-.

lemma feqg_inv_gen_dx (S):
      reflexive … S →
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ →
      ∧∧ G1 = G2 & L1 ≛[S,T2] L2 & T1 ≛[S] T2.
#S #HS #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=6 by teqg_reqg_conf_sn, and3_intro/
qed-.

(* Basic forward lemmas *****************************************************)

lemma feqg_fwd_teqg (S):
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → T1 ≛[S] T2.
#S #G1 #G2 #L1 #L2 #T1 #T2 #H
elim (feqg_inv_gen_sn … H) -H //
qed-.

lemma feqg_fwd_reqg_sn (S):
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → L1 ≛[S,T1] L2.
#S #G1 #G2 #L1 #L2 #T1 #T2 #H
elim (feqg_inv_gen_sn … H) -H //
qed-.

lemma feqg_fwd_reqg_dx (S):
      reflexive … S →
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → L1 ≛[S,T2] L2.
#S #HS #G1 #G2 #L1 #L2 #T1 #T2 #H
elim (feqg_inv_gen_dx … H) -H //
qed-.

(* Basic_2A1: removed theorems 6:
              fleq_refl fleq_sym fleq_inv_gen
              fleq_trans fleq_canc_sn fleq_canc_dx
*)
