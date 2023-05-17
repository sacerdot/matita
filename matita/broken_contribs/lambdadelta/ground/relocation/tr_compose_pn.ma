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

include "ground/relocation/tr_pn_tls.ma".
include "ground/relocation/tr_pap_pn.ma".
include "ground/relocation/tr_compose.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS ************************************)

(* Constructions with tr_push and tr_next ***********************************)

lemma tr_compose_push_bi (f2) (f1):
      (⫯(f2•f1)) = (⫯f2)•(⫯f1).
#f2 #f1
<tr_compose_unfold //
qed.

lemma tr_compose_push_next (f2) (f1):
      ↑(f2•f1) = (⫯f2)•(↑f1).
#f2 * #p1 #f1
<tr_next_unfold <tr_compose_unfold <tr_compose_unfold <tr_next_unfold
<tr_pap_push >nsucc_inj //
qed.

(* Note: to be removed *)
(*** compose_next *)
fact tr_compose_next_sn_aux (f2) (f1):
     ∀f. f2•f1 = f → (↑f2)•f1 = ↑f.
#f2 * #p1 #f1 #f
<tr_compose_unfold <tr_compose_unfold * -f
<tr_pap_next 
/3 width=1 by compose_repl_fwd_dx/
qed-.

lemma tr_compose_next_sn (f2) (f1):
      ↑(f2•f1) = (↑f2)•f1.
/2 width=1 by tr_compose_next_sn_aux/ qed.

(* Inversions with tr_push and tr_next **************************************)

(*** compose_inv_O2 *)
lemma tr_compose_inv_push_dx (f2) (f1):
      ∀f,p2,p. (p2⨮f2)•(⫯f1) = p⨮f →
      ∧∧ p2 = p & f2•f1 = f.
#f2 #f1 #f #p2 #p
<tr_compose_unfold #H destruct
/2 width=1 by conj/
qed-.

(*** compose_inv_S1 *)
lemma tr_compose_inv_next_sn (f2) (f1):
      ∀f,p1,p. (↑f2)•(p1⨮f1) = p⨮f →
      ∧∧ ↑(f2＠⧣❨p1❩) = p & f2•(p1⨮f1) = f2＠⧣❨p1❩⨮f.
#f2 #f1 #f #p1 #p
<tr_compose_unfold #H destruct
/2 width=1 by conj/
qed-.
