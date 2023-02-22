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



include "deriv.ma".

theorem p_plus_p_p: ∀f:F. ∀g:F. (fpari f ∧ fpari g) → fpari (f + g).
 assume f:F.
 assume g:F.
 suppose (fpari f ∧ fpari g) (h).
 by h we have (fpari f) (H) and (fpari g) (K).
 we need to prove (fpari (f + g))
 or equivalently ((f + g) = (f + g) ∘ ρ).
 conclude
    (f + g)
  = (f + (g ∘ ρ)) by _.
  = ((f ∘ ρ) + (g ∘ ρ)) by _.
  = ((f + g) ∘ ρ) by _
 done.
qed.

theorem p_mult_p_p: ∀f:F. ∀g:F. (fpari f ∧ fpari g) → fpari (f · g).
 assume f:F.
 assume g:F.
 suppose (fpari f ∧ fpari g) (h).
 by h we have (fpari f) (H) and (fpari g) (K).
 we need to prove (fpari (f · g))
 or equivalently ((f · g) = (f · g) ∘ ρ).
 conclude
    (f · g)
  = (f · (g ∘ ρ)) by _.
  = ((f ∘ ρ) · (g ∘ ρ)) by _.
  = ((f · g) ∘ ρ) by _
 done.
qed.

theorem d_plus_d_d: ∀f:F. ∀g:F. (fdispari f ∧ fdispari g) → fdispari (f + g).
 assume f:F.
 assume g:F.
 suppose (fdispari f ∧ fdispari g) (h).
 by h we have (fdispari f) (H) and (fdispari g) (K).
 we need to prove (fdispari (f + g))
 or equivalently ((f + g) = (ρ ∘ ((f + g) ∘ ρ))).
 conclude
    (f + g)
  = (f + (ρ ∘ (g ∘ ρ))) by _.
  = ((ρ ∘ (f ∘ ρ)) + (ρ ∘ (g ∘ ρ))) by _.
  = (((-R1) · (f ∘ ρ)) + (ρ ∘ (g ∘ ρ))) by _.
  = (((i (-R1)) · (f ∘ ρ)) + ((i (-R1)) · (g ∘ ρ))) by _.
  = (((f ∘ ρ) · (i (-R1))) + ((g ∘ ρ) · (i (-R1)))) by _.
  = (((f ∘ ρ) + (g ∘ ρ)) · (i (-R1))) by _.
  = ((i (-R1)) · ((f + g) ∘ ρ)) by _.
  = (ρ ∘ ((f + g) ∘ ρ)) by _
 done.
qed.

theorem d_mult_d_p: ∀f:F. ∀g:F. (fdispari f ∧ fdispari g) → fpari (f · g).
 assume f:F.
 assume g:F.
 suppose (fdispari f ∧ fdispari g) (h).
 by h we have (fdispari f) (h1) and (fdispari g) (h2).
 we need to prove (fpari (f · g))
 or equivalently ((f · g) = (f · g) ∘ ρ).
 conclude
    (f · g)
  = (f · (ρ ∘ (g ∘ ρ))) by _.
  = ((ρ ∘ (f ∘ ρ)) · (ρ ∘ (g ∘ ρ))) by _.
  = (((-R1) · (f ∘ ρ)) · (ρ ∘ (g ∘ ρ))) by _.
  = (((-R1) · (f ∘ ρ)) · ((-R1) · (g ∘ ρ))) by _.
  = ((-R1) · (f ∘ ρ) · (-R1) · (g ∘ ρ)) by _.
  = ((-R1) · ((f ∘ ρ) · (-R1)) · (g ∘ ρ)) by _.
  = ((-R1) · (-R1) · (f ∘ ρ) · (g ∘ ρ)) by _.
  = (R1 · ((f ∘ ρ) · (g ∘ ρ))) by _.
  = (((f ∘ ρ) · (g ∘ ρ))) by _.
  = ((f · g) ∘ ρ) by _
 done.
qed.

theorem p_mult_d_p: ∀f:F. ∀g:F. (fpari f ∧ fdispari g) → fdispari (f · g).
 assume f:F.
 assume g:F.
 suppose (fpari f ∧ fdispari g) (h).
 by h we have (fpari f) (h1) and (fdispari g) (h2).
 we need to prove (fdispari (f · g))
 or equivalently ((f · g) = ρ ∘ ((f · g) ∘ ρ)).
 conclude
    (f · g)
  = (f · (ρ ∘ (g ∘ ρ))) by _.
  = ((f ∘ ρ) · (ρ ∘ (g ∘ ρ))) by _.
  = ((f ∘ ρ) · ((-R1) · (g ∘ ρ))) by _.
  = ((-R1) · ((f ∘ ρ) · (g ∘ ρ))) by _.
  = ((-R1) · ((f · g) ∘ ρ)) by _.
  = (ρ ∘ ((f · g) ∘ ρ)) by _
 done.
qed.

theorem p_plus_c_p: ∀f:F. ∀x:R. fpari f → fpari (f + (i x)).
 assume f:F.
 assume x:R.
 suppose (fpari f) (h).
 we need to prove (fpari (f + (i x)))
 or equivalently (f + (i x) = (f + (i x)) ∘ ρ).
 by _ done.
qed.

theorem p_mult_c_p: ∀f:F. ∀x:R. fpari f → fpari (f · (i x)).
 assume f:F.
 assume x:R.
 suppose (fpari f) (h).
 we need to prove (fpari (f · (i x)))
 or equivalently ((f · (i x)) = (f · (i x)) ∘ ρ).
 by _ done.
qed.

theorem d_mult_c_d: ∀f:F. ∀x:R. fdispari f → fdispari (f · (i x)).
 assume f:F.
 assume x:R.
 suppose (fdispari f) (h).
 rewrite < fmult_commutative.
 by _ done.
qed.

theorem d_comp_d_d: ∀f,g:F. fdispari f → fdispari g → fdispari (f ∘ g).
 assume f:F.
 assume g:F.
 suppose (fdispari f) (h1).
 suppose (fdispari g) (h2).
 we need to prove (fdispari (f ∘ g))
 or equivalently (f ∘ g = ρ ∘ ((f ∘ g) ∘ ρ)).
 conclude
    (f ∘ g)
  = (ρ ∘ (f ∘ ρ) ∘ g) by _.
  = (ρ ∘ (f ∘ ρ) ∘ ρ ∘ (g ∘ ρ)) by _.
  = (ρ ∘ f ∘ (ρ ∘ ρ) ∘ (g ∘ ρ)) by _.
  = (ρ ∘ f ∘ id ∘ (g ∘ ρ)) by _.
  = (ρ ∘ ((f ∘ g) ∘ ρ)) by _
 done.
qed.

theorem pari_in_dispari: ∀ f:F. fpari f → fdispari f '.
 assume f:F. 
 suppose (fpari f) (h1).
 we need to prove (fdispari f ')
 or equivalently (f ' = ρ ∘ (f ' ∘ ρ)).
 conclude 
    (f ')
  = ((f ∘ ρ) ') by _. (*h1*)
  = ((f ' ∘ ρ) · ρ ') by _. (*demult*)
  = ((f ' ∘ ρ) · -R1) by _. (*deinv*)
  = ((-R1) · (f ' ∘ ρ)) by _. (*fmult_commutative*)
  = (ρ ∘ (f ' ∘ ρ)) (*reflex_ok*) by _
 done.
qed.

theorem dispari_in_pari: ∀ f:F. fdispari f → fpari f '.
 assume f:F. 
 suppose (fdispari f) (h1).
 we need to prove (fpari f ')
 or equivalently (f ' = f ' ∘ ρ).
 conclude 
    (f ')
  = ((ρ ∘ (f ∘ ρ)) ') by _.
  = ((ρ ' ∘ (f ∘ ρ)) · ((f ∘ ρ) ')) by _.
  = (((-R1) ∘ (f ∘ ρ)) · ((f ∘ ρ) ')) by _.
  = (((-R1) ∘ (f ∘ ρ)) · ((f ' ∘ ρ) · (-R1))) by _.
  = ((-R1) · ((f ' ∘ ρ) · (-R1))) by _.
  = (((f ' ∘ ρ) · (-R1)) · (-R1)) by _.
  = ((f ' ∘ ρ) · ((-R1) · (-R1))) by _.
  = ((f ' ∘ ρ) · R1) by _.
  = (f ' ∘ ρ) by _
 done.
qed.

alias symbol "plus" = "natural plus".
alias num (instance 0) = "natural number".
theorem de_prodotto_funzioni:
 ∀ n:nat. (id ^ (n + 1)) ' = ((n + 1)) · (id ^ n).
 assume n:nat.
 we proceed by induction on n to prove
   ((id ^ (n + 1)) ' = (i (n + 1)) · (id ^ n)).
 case O.
  we need to prove ((id ^ (0 + 1)) ' = (i 1) · (id ^ 0)).
  conclude
     ((id ^ (0 + 1)) ')
   = ((id ^ 1) ') by _.
   = ((id · (id ^ 0)) ') by _.
   = ((id · R1) ') by _.
   = (id ') by _.
   = (i R1) by _.
   = (i R1 · R1) by _.
   = (i (R0 + R1) · R1) by _.
   = (1 · (id ^ 0)) by _
 done.
 case S (n:nat).
  by induction hypothesis we know
     ((id ^ (n + 1)) ' = ((n + 1)) · (id ^ n)) (H).
  we need to prove
     ((id ^ ((n + 1)+1)) '
   = (i ((n + 1)+1)) · (id ^ (n+1))).
  conclude
     ((id ^ ((n + 1) + 1)) ')
   = ((id ^ ((n + (S 1)))) ') by _.
   = ((id ^ (S (n + 1))) ') by _.
   = ((id · (id ^ (n + 1))) ') by _.
   = ((id ' · (id ^ (n + 1))) + (id · (id ^ (n + 1)) ')) by _.
   alias symbol "plus" (instance 1) = "function plus".
   = ((R1 · (id ^ (n + 1))) + (id · (((n + 1)) · (id ^ n)))) by _.
   = ((R1 · (id ^ (n + 1))) + (((n + 1) · id · (id ^ n)))) by _.
   = ((R1 · (id ^ (n + 1))) + ((n + 1) · (id ^ (1 + n)))) by _.
   = ((R1 · (id ^ (n + 1))) + ((n + 1) · (id ^ (n + 1)))) by _.
   alias symbol "plus" (instance 2) = "function plus".
   = (((R1 + (n + 1))) · (id ^ (n + 1))) by _.
   = ((1 + (n + 1)) · (id ^ (n + 1))) by _;
   = ((n + 1 + 1) · (id ^ (n + 1))) by _
  done.
qed.

let rec times (n:nat) (x:R) on n: R ≝
 match n with
 [ O ⇒ R0
 | S n ⇒ Rplus x (times n x)
 ].

axiom invS: nat→R.
axiom invS1: ∀n:nat. Rmult (invS n) (real_of_nat (n + 1)) = R1.
axiom invS2: invS 1 + invS 1 = R1. (*forse*)

axiom e:F.
axiom deriv_e: e ' = e.
axiom e1: e · (e ∘ ρ) = R1.

(*
theorem decosh_senh:
   (invS 1 · (e + (e ∘ ρ)))' = (invS 1 · (e + (ρ ∘ (e ∘ ρ)))).
*)
