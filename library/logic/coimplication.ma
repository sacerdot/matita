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



include "logic/connectives.ma".

definition Iff : Prop \to Prop \to Prop \def
   \lambda A,B. (A \to B) \land (B \to A).
   
 (*CSC: the URI must disappear: there is a bug now *)
interpretation "logical iff" 'iff x y = (cic:/matita/logic/coimplication/Iff.con x y).

notation > "hvbox(a break \liff b)" 
  left associative with precedence 25
for @{ 'iff $a $b }.

notation < "hvbox(a break \leftrightarrow b)" 
  left associative with precedence 25
for @{ 'iff $a $b }.

theorem iff_intro: \forall A,B. (A \to B) \to (B \to A) \to (A \liff B).
 unfold Iff. intros. split; intros; autobatch.
qed.

theorem iff_refl: \forall A. A \liff A.
 intros. apply iff_intro; intros; autobatch.
qed.

theorem iff_sym: \forall A,B. A \liff B \to B \liff A.
 intros. elim H. apply iff_intro[assumption|assumption]
qed.

theorem iff_trans: \forall A,B,C. A \liff B \to B \liff C \to A \liff C.
 intros. elim H. elim H1. apply iff_intro;intros;autobatch.
qed.
