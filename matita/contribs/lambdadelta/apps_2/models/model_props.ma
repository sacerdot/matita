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

include "apps_2/models/model_vlift.ma".

(* MODEL ********************************************************************)

record is_model (M): Prop ≝ {
(* Note: equivalence: reflexivity *)
   mr: reflexive … (sq M);
(* Note: equivalence: compatibility *)
   mq: replace_2 … (sq M) (sq M) (sq M);
(* Note: application: compatibility *)
   mp: compatible_3 … (ap M) (sq M) (sq M) (sq M);
(* Note: interpretation: sort *)
   ms: ∀gv,lv,s. ⟦⋆s⟧{M}[gv, lv] ≗ sv M s;
(* Note: interpretation: local reference *)
   ml: ∀gv,lv,i. ⟦#i⟧{M}[gv, lv] ≗ lv i;
(* Note: interpretation: global reference *)
   mg: ∀gv,lv,l. ⟦§l⟧{M}[gv, lv] ≗ gv l;
(* Note: interpretation: local δ-equivalence *)
   md: ∀gv,lv,p,V,T. ⟦ⓓ{p}V.T⟧{M}[gv, lv] ≗ ⟦T⟧[gv, ⫯[0←⟦V⟧[gv, lv]]lv];
(* Note: interpretation: intensional abstraction *)
   mi: ∀gv1,gv2,lv1,lv2,p,W,T. ⟦W⟧{M}[gv1, lv1] ≗ ⟦W⟧{M}[gv2, lv2] →
       (∀d. ⟦T⟧{M}[gv1, ⫯[0←d]lv1] ≗ ⟦T⟧{M}[gv2, ⫯[0←d]lv2]) →
       ⟦ⓛ{p}W.T⟧[gv1, lv1] ≗ ⟦ⓛ{p}W.T⟧[gv2, lv2];
(* Note: interpretation: application *)
   ma: ∀gv,lv,V,T. ⟦ⓐV.T⟧{M}[gv, lv] ≗ ⟦V⟧[gv, lv] @ ⟦T⟧[gv, lv];
(* Note: interpretation: ϵ-equivalence *)
   me: ∀gv,lv,W,T. ⟦ⓝW.T⟧{M}[gv, lv] ≗ ⟦T⟧[gv, lv];
(* Note: interpretation: β-requivalence *)
   mb: ∀gv,lv,d,p,W,T. d @ ⟦ⓛ{p}W.T⟧{M}[gv, lv] ≗ ⟦T⟧[gv, ⫯[0←d]lv]
}.

record is_extensional (M): Prop ≝ {
(* Note: interpretation: extensional abstraction *)
   mx: ∀gv1,gv2,lv1,lv2,p,W1,W2,T1,T2. ⟦W1⟧{M}[gv1, lv1] ≗ ⟦W2⟧{M}[gv2, lv2] →
       (∀d. ⟦T1⟧{M}[gv1, ⫯[0←d]lv1] ≗ ⟦T2⟧{M}[gv2, ⫯[0←d]lv2]) →
       ⟦ⓛ{p}W1.T1⟧[gv1, lv1] ≗ ⟦ⓛ{p}W2.T2⟧[gv2, lv2]
}.

(* Basic properties *********************************************************)

lemma seq_sym (M): is_model M → symmetric … (sq M).
/3 width=5 by mq, mr/ qed-.

lemma seq_trans (M): is_model M → Transitive … (sq M).
/3 width=5 by mq, mr/ qed-.

lemma seq_canc_sn (M): is_model M → left_cancellable … (sq M).
/3 width=3 by seq_trans, seq_sym/ qed-.

lemma seq_canc_dx (M): is_model M → right_cancellable … (sq M).
/3 width=3 by seq_trans, seq_sym/ qed-.

lemma ti_lref_vlift_eq (M): is_model M →
                            ∀gv,lv,d,i. ⟦#i⟧[gv,⫯[i←d]lv] ≗{M} d.
#M #HM #gv #lv #d #i
@(seq_trans … HM) [2: @ml // | skip ]
>vlift_eq /2 width=1 by mr/
qed.

lemma ti_lref_vlift_gt (M): is_model M →
                            ∀gv,lv,d,i. ⟦#(↑i)⟧[gv,⫯[0←d]lv] ≗{M} ⟦#i⟧[gv,lv].
#M #HM #gv #lv #d #i
@(mq … HM) [4,5: @(seq_sym … HM) /2 width=2 by ml/ |1,2: skip ]
>vlift_gt /2 width=1 by mr/
qed.

(* Basic Forward lemmas *****************************************************)

lemma ti_fwd_mx_dx (M): is_model M →
                        ∀gv1,gv2,lv1,lv2,p,W1,W2,T1,T2.
                        ⟦ⓛ{p}W1.T1⟧[gv1, lv1] ≗ ⟦ⓛ{p}W2.T2⟧[gv2, lv2] →
                        ∀d. ⟦T1⟧{M}[gv1, ⫯[0←d]lv1] ≗ ⟦T2⟧{M}[gv2, ⫯[0←d]lv2].
#M #HM #gv1 #gv2 #lv1 #lv2 #p #W1 #W2 #T1 #T2 #H12 #d
@(mq … HM) /3 width=5 by mb, mp, mr/
qed-.
