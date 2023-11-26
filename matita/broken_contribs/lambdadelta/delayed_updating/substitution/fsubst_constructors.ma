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

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".
include "ground/lib/subset_or_eq.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Constructions with constructors for prototerm ****************************)

lemma fsubst_abst_hd (t) (u1) (u2):
      (𝛌.⬕[u1←u2]t) ⇔ ⬕[𝗟◗u1←𝗟◗u2]𝛌.t.
// qed.

lemma fsubst_appl_sd (v) (t) (u1) (u2):
      ＠⬕[u1←u2]v.t ⇔ ⬕[𝗦◗u1←𝗦◗u2]＠v.t.
#v #t #u1 #u2
@subset_eq_trans [|| @fsubst_or ]
@subset_eq_trans [|| @subset_or_eq_repl ]
[5: @fsubst_lcons_neq #H0 destruct |4: skip ] //
qed.

lemma fsubst_appl_hd (v) (t) (u1) (u2):
      ＠v.⬕[u1←u2]t ⇔ ⬕[𝗔◗u1←𝗔◗u2]＠v.t.
#v #t #u1 #u2
@subset_eq_trans [|| @fsubst_or ]
@subset_eq_trans [|| @subset_or_eq_repl ]
[3: @fsubst_lcons_neq #H0 destruct |2: skip ] //
qed.
