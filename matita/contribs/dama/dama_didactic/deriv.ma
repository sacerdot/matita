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



include "reals.ma".

axiom F:Type.(*F=funzioni regolari*)
axiom fplus:F→F→F.
axiom fmult:F→F→F.
axiom fcomp:F→F→F.

axiom De: F→F. (*funzione derivata*)
notation "a '"
  non associative with precedence 80
for @{ 'deriv $a }.
interpretation "function derivative" 'deriv x = (De x). 
interpretation "function mult" 'mult x y = (fmult x y). 
interpretation "function compositon" 'compose x y = (fcomp x y).

notation "hvbox(a break + b)"
  right associative with precedence 45
for @{ 'oplus $a $b }.

interpretation "function plus" 'plus x y = (fplus x y).

axiom i:R→F. (*mappatura  R in F*)
coercion cic:/matita/didactic/deriv/i.con.
axiom i_comm_plus: ∀x,y:R. (i (x+y)) = (i x) + (i y).
axiom i_comm_mult: ∀x,y:R. (i (Rmult x y)) = (i x) · (i y).

axiom freflex:F.
notation "ρ"
  non associative with precedence 100
for @{ 'rho }.
interpretation "function flip" 'rho = freflex.
axiom reflex_ok: ∀f:F. ρ ∘ f = (i (-R1)) · f.
axiom dereflex: ρ ' = i (-R1). (*Togliere*)

axiom id:F. (* Funzione identita' *)
axiom fcomp_id_neutral: ∀f:F. f ∘ id = f.
axiom fcomp_id_commutative: ∀f:F. f ∘ id = id ∘ f.
axiom deid: id ' = i R1.
axiom rho_id: ρ ∘ ρ = id.

lemma rho_disp: ρ = ρ ∘ (ρ ∘ ρ).
 we need to prove (ρ = ρ ∘ (ρ ∘ ρ)).
 by _ done.
qed.

lemma id_disp: id = ρ ∘ (id ∘ ρ).
 we need to prove (id = ρ ∘ (id ∘ ρ)).
 by _ done.
qed.

let rec felev (f:F) (n:nat) on n: F ≝
 match n with
 [ O ⇒ i R1
 | S n ⇒ f · (felev f n)
 ].

(* Proprietà *)

axiom fplus_commutative: ∀ f,g:F. f + g = g + f.
axiom fplus_associative: ∀ f,g,h:F. f + (g + h) = (f + g) + h.
axiom fplus_neutral: ∀f:F. (i R0) + f = f.
axiom fmult_commutative: ∀ f,g:F. f · g = g · f.
axiom fmult_associative: ∀ f,g,h:F. f · (g · h) = (f · g) · h.
axiom fmult_neutral: ∀f:F. (i R1) · f = f.
axiom fmult_assorb: ∀f:F. (i R0) · f = (i R0).
axiom fdistr: ∀ f,g,h:F. (f + g) · h = (f · h) + (g · h).
axiom fcomp_associative: ∀ f,g,h:F. f ∘ (g ∘ h) = (f ∘ g) ∘ h.

axiom fcomp_distr1: ∀ f,g,h:F. (f + g) ∘ h = (f ∘ h) + (g ∘ h).
axiom fcomp_distr2: ∀ f,g,h:F. (f · g) ∘ h = (f ∘ h) · (g ∘ h).

axiom demult: ∀ f,g:F. (f · g) ' = (f ' · g) + (f · g ').
axiom decomp: ∀ f,g:F. (f ∘ g) ' = (f ' ∘ g) · g '.
axiom deplus: ∀ f,g:F. (f + g) ' = (f ') + (g ').

axiom cost_assorb: ∀x:R. ∀f:F. (i x) ∘ f = i x.
axiom cost_deriv: ∀x:R. (i x) ' = i R0.


definition fpari ≝ λ f:F. f = f ∘ ρ.
definition fdispari ≝ λ f:F. f = ρ ∘ (f ∘ ρ).
axiom cost_pari: ∀ x:R. fpari (i x).

axiom meno_piu_i: (i (-R1)) · (i (-R1)) = i R1.

notation "hvbox(a break ^ b)"
  right associative with precedence 75
for @{ 'elev $a $b }.
 
interpretation "function power" 'elev x y = (felev x y). 

axiom tech1: ∀n,m. F_OF_nat n + F_OF_nat m = F_OF_nat (n + m).
