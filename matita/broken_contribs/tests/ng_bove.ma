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

include "logic/pts.ma".

include "nat/minus.ma".

ninductive D: nat → Prop ≝
   D0: D O
 | Dn: ∀n. D (n - 2) → D n.
 
naxiom dow: ∀n,m.∀p: D n. n = S m → False.
naxiom destr: ∀n. O = S n → False.

nlet rec f (n:nat) (p:D n) on p : nat ≝
 match n return λm. n=m → nat with
  [ O ⇒ λ_.O
  | S m ⇒ λH. f (n - 2) ?] (refl_eq ? n).
 ncases p in H
  [ #K; ncases (destr ? K)
  | #n0; #p; #H; nassumption ]
nqed.