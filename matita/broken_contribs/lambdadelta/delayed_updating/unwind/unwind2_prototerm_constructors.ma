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

include "delayed_updating/unwind/unwind2_prototerm_eq.ma".
include "delayed_updating/unwind/unwind2_path_append.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with constructors for prototerm ****************************)

lemma unwind2_term_oref_xapp (f) (k):
      (⧣(f＠❨k❩)) ⇔ ▼[f]⧣k.
#f #k @conj #p *
[ /2 width=1 by in_comp_unwind2_bi/
| #q * #H0 destruct //
]
qed.

lemma unwind2_term_iref (f) (t) (k):
      t ⊆ 𝐏 → ▼[f•𝐮❨k❩]t ⇔ ▼[f](𝛕k.t).
#f #t #k #Ht @conj
#p * #q #Hq #H0 destruct
[ lapply (Ht … Hq) -Ht #H0
  elim (ppc_inv_lcons … H0) -H0 #r #l #H0 destruct
  /3 width=1 by in_comp_unwind2_bi, in_comp_iref_hd/
| elim (in_comp_inv_iref … Hq) -Hq #p #H0 #Hp destruct
  lapply (Ht … Hp) -Ht #H0
  elim (ppc_inv_lcons … H0) -H0 #r #l #H0 destruct
  /2 width=1 by in_comp_unwind2_bi/
]
qed.

lemma unwind2_term_abst (f) (t):
      (𝛌.▼[⫯f]t) ⇔ ▼[f]𝛌.t.
#f #t @conj #p #Hp
[ elim (in_comp_inv_abst … Hp) -Hp #q #H1 * #r #Hr #H2 destruct
  /3 width=1 by in_comp_unwind2_bi, in_comp_abst_hd/
| elim Hp -Hp #q #Hq #H0 destruct
  elim (in_comp_inv_abst … Hq) -Hq #r #H0 #Hr destruct
  /3 width=1 by in_comp_unwind2_bi, in_comp_abst_hd/
]
qed.

lemma unwind2_term_appl (f) (v) (t):
      ＠▼[f]v.▼[f]t ⇔ ▼[f]＠v.t.
#f #v #t @conj #p #Hp
[ elim (in_comp_inv_appl … Hp) -Hp * #q #H1 * #r #Hr #H2 destruct
  /3 width=1 by in_comp_unwind2_bi, in_comp_appl_sd, in_comp_appl_hd/
| elim Hp -Hp #q #Hq #H0 destruct
  elim (in_comp_inv_appl … Hq) -Hq * #r #H0 #Hr destruct
  /3 width=1 by in_comp_unwind2_bi, in_comp_appl_sd, in_comp_appl_hd/
]
qed.
