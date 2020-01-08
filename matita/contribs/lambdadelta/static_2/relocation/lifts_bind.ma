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

include "static_2/syntax/ext2.ma".
include "static_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR BINDERS *******************************************)

definition liftsb: rtmap → relation bind ≝
           λf. ext2 (lifts f).

interpretation "uniform relocation (binder for local environments)"
   'RLiftStar i I1 I2 = (liftsb (uni i) I1 I2).

interpretation "generic relocation (binder for local environments)"
   'RLiftStar f I1 I2 = (liftsb f I1 I2).

(* Basic_inversion lemmas **************************************************)

lemma liftsb_inv_unit_sn: ∀f,I,Z2. ⇧*[f] BUnit I ≘ Z2 → Z2 = BUnit I.
/2 width=2 by ext2_inv_unit_sn/ qed-.

lemma liftsb_inv_pair_sn: ∀f:rtmap. ∀Z2,I,V1. ⇧*[f] BPair I V1 ≘ Z2 →
                          ∃∃V2. ⇧*[f] V1 ≘ V2 & Z2 = BPair I V2.
/2 width=1 by ext2_inv_pair_sn/ qed-.

lemma liftsb_inv_unit_dx: ∀f,I,Z1. ⇧*[f] Z1 ≘ BUnit I → Z1 = BUnit I.
/2 width=2 by ext2_inv_unit_dx/ qed-.

lemma liftsb_inv_pair_dx: ∀f:rtmap. ∀Z1,I,V2. ⇧*[f] Z1 ≘ BPair I V2 →
                          ∃∃V1. ⇧*[f] V1 ≘ V2 & Z1 = BPair I V1.
/2 width=1 by ext2_inv_pair_dx/ qed-.

(* Basic properties *********************************************************)

lemma liftsb_eq_repl_back: ∀I1,I2. eq_repl_back … (λf. ⇧*[f] I1 ≘ I2).
#I1 #I2 #f1 * -I1 -I2 /3 width=3 by lifts_eq_repl_back, ext2_pair/
qed-.

lemma liftsb_refl: ∀f. 𝐈❪f❫ → reflexive … (liftsb f).
/3 width=1 by lifts_refl, ext2_refl/ qed.

lemma liftsb_total: ∀I1,f. ∃I2. ⇧*[f] I1 ≘ I2.
* [2: #I #T1 #f elim (lifts_total T1 f) ]
/3 width=2 by ext2_unit, ext2_pair, ex_intro/
qed-.

lemma liftsb_split_trans: ∀f,I1,I2. ⇧*[f] I1 ≘ I2 →
                          ∀f1,f2. f2 ⊚ f1 ≘ f →
                          ∃∃I. ⇧*[f1] I1 ≘ I & ⇧*[f2] I ≘ I2.
#f #I1 #I2 * -I1 -I2 /2 width=3 by ext2_unit, ex2_intro/
#I #V1 #V2 #HV12 #f1 #f2 #Hf elim (lifts_split_trans … HV12 … Hf) -f
/3 width=3 by ext2_pair, ex2_intro/
qed-.

(* Basic forward lemmas *****************************************************)

lemma liftsb_fwd_isid: ∀f,I1,I2. ⇧*[f] I1 ≘ I2 → 𝐈❪f❫ → I1 = I2.
#f #I1 #I2 * -I1 -I2 /3 width=3 by lifts_fwd_isid, eq_f2/
qed-.
