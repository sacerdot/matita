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
   mq: reflexive … (sq M);
   mr: replace_2 … (sq M) (sq M) (sq M);
   mc: compatible_3 … (ap M) (sq M) (sq M) (sq M);
   ms: ∀gv,lv,s. ⟦⋆s⟧{M}[gv, lv] ≗ sv M s;
   ml: ∀gv,lv,i. ⟦#i⟧{M}[gv, lv] ≗ lv i;
   mg: ∀gv,lv,l. ⟦§l⟧{M}[gv, lv] ≗ gv l;
   md: ∀gv,lv,p,V,T. ⟦ⓓ{p}V.T⟧{M}[gv, lv] ≗ ⟦T⟧[gv, ⫯[⟦V⟧[gv, lv]]lv];
   mi: ∀gv,lv1,lv2,p,W,T. ⟦W⟧{M}[gv, lv1] ≗ ⟦W⟧{M}[gv, lv2] →
       (∀d. ⟦T⟧{M}[gv, ⫯[d]lv1] ≗ ⟦T⟧{M}[gv, ⫯[d]lv2]) →
       ⟦ⓛ{p}W.T⟧[gv, lv1] ≗ ⟦ⓛ{p}W.T⟧[gv, lv2];
   ma: ∀gv,lv,V,T. ⟦ⓐV.T⟧{M}[gv, lv] ≗ ⟦V⟧[gv, lv] @ ⟦T⟧[gv, lv];
   me: ∀gv,lv,W,T. ⟦ⓝW.T⟧{M}[gv, lv] ≗ ⟦T⟧[gv, lv];
   mb: ∀gv,lv,d,p,W,T. d @ ⟦ⓛ{p}W.T⟧{M}[gv, lv] ≗ ⟦T⟧[gv, ⫯[d]lv]
}.

record is_extensional (M): Prop ≝ {
   mx: ∀gv,lv1,lv2,p,W1,W2,T1,T2. ⟦W1⟧{M}[gv, lv1] ≗ ⟦W2⟧{M}[gv, lv2] →
       (∀d. ⟦T1⟧{M}[gv, ⫯[d]lv1] ≗ ⟦T2⟧{M}[gv, ⫯[d]lv2]) →
       ⟦ⓛ{p}W1.T1⟧[gv, lv1] ≗ ⟦ⓛ{p}W2.T2⟧[gv, lv2]
}.

(* Basic properties *********************************************************)

lemma seq_sym (M): is_model M → symmetric … (sq M).
/3 width=5 by mr, mq/ qed-.

lemma seq_trans (M): is_model M → Transitive … (sq M).
/3 width=5 by mr, mq/ qed-.

lemma seq_canc_sn (M): is_model M → left_cancellable … (sq M).
/3 width=3 by seq_trans, seq_sym/ qed-.

lemma seq_canc_dx (M): is_model M → right_cancellable … (sq M).
/3 width=3 by seq_trans, seq_sym/ qed-.

lemma ti_lref_vlift_eq (M): is_model M →
                            ∀gv,lv,d,i. ⟦#i⟧[gv,⫯[i←d]lv] ≗{M} d.
#M #HM #gv #lv #d #i
@(seq_trans … HM) [2: @ml // | skip ]
>vlift_eq /2 width=1 by mq/
qed.

lemma ti_lref_vlift_gt (M): is_model M →
                            ∀gv,lv,d,i. ⟦#(↑i)⟧[gv,⫯[d]lv] ≗{M} ⟦#i⟧[gv,lv].
#M #HM #gv #lv #d #i
@(mr … HM) [4,5: @(seq_sym … HM) @(ml … HM) |1,2: skip ]
>vlift_gt /2 width=1 by mq/
qed.
