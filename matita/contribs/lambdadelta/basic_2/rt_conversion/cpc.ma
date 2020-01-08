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

include "basic_2/notation/relations/pconv_5.ma".
include "basic_2/rt_transition/cpm.ma".

(* CONTEXT-SENSITIVE PARALLEL R-CONVERSION FOR TERMS ************************)

definition cpc: sh → relation4 genv lenv term term ≝
                λh,G,L,T1,T2. ❪G,L❫ ⊢ T1 ➡[h] T2 ∨ ❪G,L❫ ⊢ T2 ➡[h] T1.

interpretation
   "context-sensitive parallel r-conversion (term)"
   'PConv h G L T1 T2 = (cpc h G L T1 T2).

(* Basic properties *********************************************************)

lemma cpc_refl: ∀h,G,L. reflexive … (cpc h G L).
/2 width=1 by or_intror/ qed.

lemma cpc_sym: ∀h,G,L. symmetric … (cpc h L G).
#h #G #L #T1 #T2 * /2 width=1 by or_introl, or_intror/
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpc_fwd_cpr: ∀h,G,L,T1,T2. ❪G,L❫ ⊢ T1 ⬌[h] T2 →
                   ∃∃T. ❪G,L❫ ⊢ T1 ➡[h] T & ❪G,L❫ ⊢ T2 ➡[h] T.
#h #G #L #T1 #T2 * /2 width=3 by ex2_intro/
qed-.
