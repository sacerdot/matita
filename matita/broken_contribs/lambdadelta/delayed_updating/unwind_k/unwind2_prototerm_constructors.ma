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

include "delayed_updating/unwind_k/unwind2_prototerm_eq.ma".
include "delayed_updating/unwind_k/unwind2_path_append.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with constructors for prototerm ****************************)

lemma unwind2_term_oref_pap (f) (k):
      (⧣(f＠⧣❨k❩)) ⇔ ▼[f]⧣k.
#f #k @conj #p *
[ /2 width=1 by in_comp_unwind2_path_term/
| #q * #H0 destruct //
]
qed.

lemma unwind2_term_iref (f) (t) (k:ℤ⁺):
      ▼[f•𝐮❨k❩]t ⇔ ▼[f](𝛕k.t).
#f #t #k @conj
#p * #q #Hq #H0 destruct
[ @(ex2_intro … (𝗱k◗𝗺◗q))
  /2 width=1 by in_comp_iref_hd/
| elim (in_comp_inv_iref … Hq) -Hq #p #Hp #Ht destruct
  /2 width=1 by in_comp_unwind2_path_term/
]
qed.

lemma unwind2_term_abst (f) (t):
      (𝛌.▼[⫯f]t) ⇔ ▼[f]𝛌.t.
#f #t @conj #p #Hp
[ elim (in_comp_inv_abst … Hp) -Hp #q #H1 * #r #Hr #H2 destruct
  /3 width=1 by in_comp_unwind2_path_term, in_comp_abst_hd/
| elim Hp -Hp #q #Hq #H0 destruct
  elim (in_comp_inv_abst … Hq) -Hq #r #H0 #Hr destruct
  /3 width=1 by in_comp_unwind2_path_term, in_comp_abst_hd/
]
qed.

lemma unwind2_term_appl (f) (v) (t):
      ＠▼[f]v.▼[f]t ⇔ ▼[f]＠v.t.
#f #v #t @conj #p #Hp
[ elim (in_comp_inv_appl … Hp) -Hp * #q #H1 * #r #Hr #H2 destruct
  /3 width=1 by in_comp_unwind2_path_term, in_comp_appl_sd, in_comp_appl_hd/
| elim Hp -Hp #q #Hq #H0 destruct
  elim (in_comp_inv_appl … Hq) -Hq * #r #H0 #Hr destruct
  /3 width=1 by in_comp_unwind2_path_term, in_comp_appl_sd, in_comp_appl_hd/
]
qed.
