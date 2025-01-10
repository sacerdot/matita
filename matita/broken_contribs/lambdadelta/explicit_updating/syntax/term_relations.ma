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

include "explicit_updating/syntax/term.ma".

(* RELATIONS FOR TERM *******************************************************)

definition term_replace_4:
           relation2 (relation2 (𝕋) (𝕋)) (relation4 (𝕋) (𝕋 ) (𝕋) (𝕋)) ≝
           λS,R. ∀t1,t2. replace_2 … S S (R t1 t2).

definition term_replace_6:
           relation2 (relation2 (𝕋) (𝕋)) (relation6 (𝕋) (𝕋) (𝕋) (𝕋 ) (𝕋) (𝕋)) ≝
           λS,R. ∀v1,v2,t1,t2. replace_2 … S S (R v1 v2 t1 t2).

definition lbot_4: relation4 (𝕋) (𝕋 ) (𝕋) (𝕋) ≝
           λt1,t2,x,y. ⊥.

definition lbot_6: relation6 (𝕋) (𝕋 ) (𝕋) (𝕋 ) (𝕋) (𝕋) ≝
           λv1,v2,t1,t2,x,y. ⊥.

(* Basic constructions ******************************************************)

lemma lbot_4_repl (S): term_replace_4 S lbot_4.
#S #t1 #t2 #x #y #H0 elim H0
qed.

lemma lbot_6_repl (S): term_replace_6 S lbot_6.
#S #v1 #v2 #t1 #t2 #x #y #H0 elim H0
qed.
