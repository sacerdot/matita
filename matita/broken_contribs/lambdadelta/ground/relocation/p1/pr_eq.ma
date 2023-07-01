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

include "ground/xoa/ex_3_2.ma".
include "ground/notation/relations/doteq_2.ma".
include "ground/lib/stream_eq.ma".
include "ground/relocation/p1/pr_map.ma".

(* EXTENSIONAL EQUIVALENCE FOR PARTIAL RELOCATION MAPS **********************)

(*** eq *)
coinductive pr_eq: relation pr_map ≝
(*** eq_push *)
| pr_eq_push (f1) (f2) (g1) (g2):
  pr_eq f1 f2 → ⫯f1 = g1 → ⫯f2 = g2 → pr_eq g1 g2
(*** eq_next *)
| pr_eq_next (f1) (f2) (g1) (g2):
  pr_eq f1 f2 → ↑f1 = g1 → ↑f2 = g2 → pr_eq g1 g2
.

interpretation
  "extensional equivalence (partial relocation maps)"
  'DotEq f1 f2 = (pr_eq f1 f2).

(*** eq_repl *)
definition pr_eq_repl (R:relation …) ≝
           ∀f1,f2. f1 ≐ f2 → R f1 f2.

(*** eq_repl_back *)
definition pr_eq_repl_back (R:predicate …) ≝
           ∀f1. R f1 → ∀f2. f1 ≐ f2 → R f2.

(*** eq_repl_fwd *)
definition pr_eq_repl_fwd (R:predicate …) ≝
           ∀f1. R f1 → ∀f2. f2 ≐ f1 → R f2.

(* Basic constructions ******************************************************)

(*** eq_sym *)
corec lemma pr_eq_sym: symmetric … pr_eq.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf #H1 #H2
[ @(pr_eq_push … H2 H1) | @(pr_eq_next … H2 H1) ] -g2 -g1 /2 width=1 by/
qed-.

(*** eq_repl_sym *)
lemma pr_eq_repl_sym (R):
      pr_eq_repl_back R → pr_eq_repl_fwd R.
/3 width=3 by pr_eq_sym/ qed-.

(* Alternative definition with stream_eq (specific) *************************)

alias symbol "subseteq" (instance 1) = "relation inclusion".

corec lemma stream_eq_pr_eq: stream_eq … ⊆ pr_eq.
* #b1 #f1 * #b2 #f2 #H
cases (stream_eq_inv_cons_bi … H) -H [|*: // ] * -b2 #Hf
cases b1 /3 width=5 by pr_eq_next, pr_eq_push/
qed.

corec lemma pr_eq_inv_stream_eq: pr_eq ⊆ stream_eq ….
#g1 #g2 * -g1 -g2 #f1 #f2 #g1 #g2 #Hf * * -g1 -g2
/3 width=1 by stream_eq_cons/
qed-.
