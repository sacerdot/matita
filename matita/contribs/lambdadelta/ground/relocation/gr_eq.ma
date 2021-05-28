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
include "ground/notation/relations/ideq_2.ma".
include "ground/lib/stream_eq.ma".
include "ground/relocation/gr_map.ma".

(* EXTENSIONAL EQUIVALENCE FOR GENERIC RELOCATION MAPS **********************)

(*** eq *)
coinductive gr_eq: relation gr_map ≝
(*** eq_push *)
| gr_eq_push (f1) (f2) (g1) (g2):
  gr_eq f1 f2 → ⫯f1 = g1 → ⫯f2 = g2 → gr_eq g1 g2
(*** eq_next *)
| gr_eq_next (f1) (f2) (g1) (g2):
  gr_eq f1 f2 → ↑f1 = g1 → ↑f2 = g2 → gr_eq g1 g2
.

interpretation
  "extensional equivalence (generic relocation maps)"
  'IdEq f1 f2 = (gr_eq f1 f2).

(*** eq_repl *)
definition gr_eq_repl (R:relation …) ≝
           ∀f1,f2. f1 ≡ f2 → R f1 f2.

(*** eq_repl_back *)
definition gr_eq_repl_back (R:predicate …) ≝
           ∀f1. R f1 → ∀f2. f1 ≡ f2 → R f2.

(*** eq_repl_fwd *)
definition gr_eq_repl_fwd (R:predicate …) ≝
           ∀f1. R f1 → ∀f2. f2 ≡ f1 → R f2.

(* Basic properties *********************************************************)

(*** eq_sym *)
corec lemma gr_eq_sym: symmetric … gr_eq.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf #H1 #H2
[ @(gr_eq_push … H2 H1) | @(gr_eq_next … H2 H1) ] -g2 -g1 /2 width=1 by/
qed-.

(*** eq_repl_sym *)
lemma gr_eq_repl_sym (R):
      gr_eq_repl_back R → gr_eq_repl_fwd R.
/3 width=3 by gr_eq_sym/ qed-.

(* Alternative definition with stream_eq (specific) ***************************************************)

alias symbol "subseteq" (instance 1) = "relation inclusion".

corec lemma stream_eq_gr_eq: stream_eq … ⊆ gr_eq.
* #b1 #f1 * #b2 #f2 #H
cases (stream_eq_inv_cons_bi … H) -H [|*: // ] * -b2 #Hf
cases b1 /3 width=5 by gr_eq_next, gr_eq_push/
qed.

corec lemma gr_eq_inv_stream_eq: gr_eq ⊆ stream_eq ….
#g1 #g2 * -g1 -g2 #f1 #f2 #g1 #g2 #Hf * * -g1 -g2
/3 width=1 by stream_eq_cons/
qed-.
