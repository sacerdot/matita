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

include "ground/notation/functions/exp_3.ma".
include "ground/lib/exteq.ma".
include "ground/arith/pnat.ma".

(* ITERATED FUNCTION FOR POSITIVE INTEGERS **********************************)

(* Note: see also: lib/arithemetics/bigops.ma *)
rec definition piter (p) (A:Type[0]) (f:A→A) (a:A): A ≝
match p with
[ punit   ⇒ f a
| psucc q ⇒ f (piter q A f a)
].

interpretation
  "iterated function (positive integers)"
  'Exp A f p = (piter p A f).

(* Basic constructions ******************************************************)

lemma piter_unit (A) (f): f ⊜ f^{A}𝟏.
// qed.

lemma piter_succ (A) (f) (p): f ∘ f^p ⊜ f^{A}(↑p).
// qed.

(* Advanced constructions ***************************************************)

lemma piter_appl (A) (f) (p): f ∘ f^p ⊜ f^{A}p ∘ f.
#A #f #p elim p -p //
#p #IH @exteq_repl
/3 width=5 by compose_repl_fwd_dx, compose_repl_fwd_sn, exteq_canc_dx/
qed.

lemma piter_compose (A) (B) (f) (g) (h) (p):
      h ∘ f ⊜ g ∘ h → h ∘ (f^{A}p) ⊜ (g^{B}p) ∘ h.
#A #B #f #g #h #p elim p -p
[ #H @exteq_repl
  /2 width=5 by compose_repl_fwd_sn, compose_repl_fwd_dx/
| #p #IH #H @exteq_repl
  [4: @compose_repl_fwd_dx [| @piter_succ ]
  |5: @compose_repl_fwd_sn [| @piter_succ ]
  |1,2: skip
  ]
  @exteq_trans [2: @compose_assoc |1: skip ]
  @exteq_trans [2: @(compose_repl_fwd_sn … H) | 1:skip ]
  @exteq_canc_sn [2: @compose_assoc |1: skip ]
  /3 width=1 by compose_repl_fwd_dx/
]
qed.
