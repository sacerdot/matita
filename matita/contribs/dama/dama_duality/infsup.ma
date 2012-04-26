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

include "sequence.ma".

definition upper_bound ≝ λO:excess.λa:sequence O.λu:O.∀n:nat.a n ≤ u.

definition weak_sup ≝
  λO:excess.λs:sequence O.λx.
    upper_bound ? s x ∧ (∀y:O.upper_bound ? s y → x ≤ y).

definition strong_sup ≝
  λO:excess.λs:sequence O.λx.upper_bound ? s x ∧ (∀y:O.x ≰ y → ∃n.s n ≰ y).

definition increasing ≝ λO:excess.λa:sequence O.∀n:nat.a n ≤ a (S n).

notation < "x \nbsp 'is_upper_bound' \nbsp s" non associative with precedence 55 for @{'upper_bound $_ $s $x}.
notation < "x \nbsp 'is_lower_bound' \nbsp s" non associative with precedence 55 for @{'lower_bound $_ $s $x}.
notation < "s \nbsp 'is_increasing'"          non associative with precedence 55 for @{'increasing $_ $s}.
notation < "s \nbsp 'is_decreasing'"          non associative with precedence 55 for @{'decreasing $_ $s}.
notation < "x \nbsp 'is_strong_sup' \nbsp s"  non associative with precedence 55 for @{'strong_sup $_ $s $x}.
notation < "x \nbsp 'is_strong_inf' \nbsp s"  non associative with precedence 55 for @{'strong_inf $_ $s $x}.

notation > "x 'is_upper_bound' s 'in' e" non associative with precedence 55 for @{'upper_bound $e $s $x}.
notation > "x 'is_lower_bound' s 'in' e" non associative with precedence 55 for @{'lower_bound $e $s $x}.
notation > "s 'is_increasing' 'in' e"    non associative with precedence 55 for @{'increasing $e $s}.
notation > "s 'is_decreasing' 'in' e"    non associative with precedence 55 for @{'decreasing $e $s}.
notation > "x 'is_strong_sup' s 'in' e"  non associative with precedence 55 for @{'strong_sup $e $s $x}.
notation > "x 'is_strong_inf' s 'in' e"  non associative with precedence 55 for @{'strong_inf $e $s $x}.

interpretation "Excess upper bound" 'upper_bound e s x = (upper_bound e s x).
interpretation "Excess lower bound" 'lower_bound e s x = (upper_bound (dual_exc e) s x).
interpretation "Excess increasing"  'increasing e s    = (increasing e s).
interpretation "Excess decreasing"  'decreasing e s    = (increasing (dual_exc e) s).
interpretation "Excess strong sup"  'strong_sup e s x  = (strong_sup e s x).
interpretation "Excess strong inf"  'strong_inf e s x  = (strong_sup (dual_exc e) s x).

lemma strong_sup_is_weak: 
  ∀O:excess.∀s:sequence O.∀x:O.strong_sup ? s x → weak_sup ? s x.
intros (O s x Ssup); elim Ssup (Ubx M); clear Ssup; split; [assumption]
intros 3 (y Uby E); cases (M ? E) (n En); unfold in Uby; cases (Uby ? En);
qed.
