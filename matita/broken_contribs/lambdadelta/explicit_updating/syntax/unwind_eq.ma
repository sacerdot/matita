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

include "ground/relocation/fb/fbr_uni_plus.ma".
include "explicit_updating/syntax/substitution_unwind_eq.ma".
include "explicit_updating/syntax/substitution_tapp_eq.ma".
include "explicit_updating/syntax/unwind_lref.ma".

(* UNWIND FOR TERM **********************************************************)

(* Constructions with term_eq ***********************************************)

lemma unwind_eq_repl:
      compatible_3 … fbr_eq term_eq term_eq unwind.
#f1 #f2 #Hf
/3 width=1 by subst_tapp_eq_repl, subst_unwind_eq_repl/
qed.

lemma unwind_abst (f) (b) (t):
      (𝛌b.▼[⫯f]t) ≐ ▼[f](𝛌b.t).
#f #b #t
<unwind_unfold <unwind_unfold <subst_tapp_abst
/3 width=1 by subst_tapp_eq_repl, term_eq_abst/
qed.

lemma unwind_lift (f) (g) (t):
      ▼[f•g]t ≐ ▼[f](𝛗g.t).
#f #g #t
<unwind_unfold <unwind_unfold <subst_tapp_lift
/2 width=1 by subst_tapp_eq_repl/
qed.

lemma unwind_id_abst (b) (t):
      (𝛌b.▼[𝐢]t) ≐ ▼[𝐢](𝛌b.t).
#b #t
@(term_eq_trans … (unwind_abst …))
/3 width=1 by unwind_eq_repl, term_eq_abst/
qed.

lemma unwind_uni_next (n) (t):
      ▼[𝐮❨⁤↑n❩]t ≐ ▼[𝐮❨n❩](↑t).
#n #t
@(term_eq_trans … (unwind_lift …))
/2 width=1 by unwind_eq_repl/
qed.

lemma subst_tapp_unwind (t) (f) (S):
      (S•f)＠⧣❨t❩ ≐ S＠⧣❨▼[f]t❩.
#t elim t -t
[ #g #S
  <subst_tapp_unit >term_lref_unit <unwind_lref <subst_tapp_lref //
| #b #t #IH #g #S
  @(term_eq_trans … (subst_tapp_eq_repl S S …))
  [2: @unwind_abst |3: skip |4: // ]
  <subst_tapp_abst <subst_tapp_abst
  @term_eq_abst
  @(term_eq_trans … (IH … (⫯g) (⫯S))) -IH
  @subst_tapp_eq_repl [| // ]
  /2 width=1 by term_eq_sym/
| #v #t #IHv #IHt #g #S
  <subst_tapp_appl <unwind_appl <subst_tapp_appl
  /2 width=1 by term_eq_appl/
| #f #t #IH #g #S
  <subst_tapp_lift
  @(term_eq_repl … (IH (g•f) S))
  /2 width=1 by subst_tapp_eq_repl/
]
qed.

(* Main constructions with term_eq ******************************************)

theorem unwind_after (g) (f) (t):
        ▼[g•f]t ≐ ▼[g]▼[f]t.
#g #f #t
<unwind_unfold <unwind_unfold
@(term_eq_trans ???? (subst_tapp_unwind …))
@(subst_tapp_eq_repl … (subst_unwind_after …)) //
qed.

lemma unwind_id_idem (f) (t):
      ▼[f]t ≐ ▼[𝐢]▼[f]t.
#f #t
@(term_eq_trans … (unwind_after …))
/2 width=1 by unwind_eq_repl/
qed.
