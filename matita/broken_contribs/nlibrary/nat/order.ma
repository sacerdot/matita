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

include "nat/nat.ma".
include "sets/sets.ma".

ninductive le (n: nat) : nat → CProp[0] ≝
   le_n: le n n
 | le_S: ∀m. le n m → le n (S m).

interpretation "natural 'less or equal to'" 'leq x y = (le x y).
interpretation "natural 'neither less nor equal to'" 'nleq x y = (Not (le x y)).

ndefinition lt ≝ λn,m. S n ≤ m.

interpretation "natural 'less than'" 'lt x y = (lt x y).
interpretation "natural 'not less than'" 'nless x y = (Not (lt x y)).

nlemma le_O_n: ∀n. le O n.
 #n; nelim n [ napply le_n | #n'; #H; napply le_S; nassumption ]
nqed.

(* needs decompose *)
naxiom le_S_S: ∀n,m. le n m → le (S n) (S m).
naxiom le_S_S_to_le: ∀n,m. le (S n) (S m) → le n m.
naxiom lt_Sn_m: ∀n,m. lt (S n) m → lt n m.
naxiom lt_to_le: ∀n,m. lt n m → le n m.
naxiom lt_le_trans: ∀n,m,p. lt n m → le m p → lt n p.

nlemma lt_O_Sn: ∀n. lt O (S n).
 #n; napply le_S_S; napply le_O_n.
nqed. 

ndefinition Nat_: nat → ext_powerclass NAT.
 #n; napply mk_ext_powerclass
  [ napply {m | m < n}
  | #x; #x'; #H; nrewrite < H; napply mk_iff; #K; nassumption (* refl non va *) ]
nqed.
