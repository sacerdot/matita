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

include "ng_pts.ma".

ndefinition thesis0: ∀A:Type.Type ≝ λA. A → A.

ndefinition thesis: ∀A:Type.Type ≝ λA. ?.
 napply (A → A);
nqed.

ntheorem foo: ∀A:Type.thesis A.#A;#x;napply x;
nqed.

ntheorem goo: ∀A:Type.A → A. #A; napply (foo ?);
nqed.

naxiom NP: Prop.

ndefinition Q: Prop ≝ NP.

include "nat/nat.ma".

nlet rec nzero (n:nat) : nat ≝
 match n with
  [ O ⇒ O
  | S m ⇒ nzero m].

ntheorem nzero_ok: nzero (S (S O)) = O.
 napply (refl_eq ? O);
nqed.

naxiom DT: nat → Type.
naxiom dt: ∀n. DT n.

ninductive nnat (n: nat) (A:DT n): Type ≝
   nO: nnat n A
 | nS: mat n A → mat n A → nnat n A
with mat: Type ≝ 
 |mS : nnat n A → mat n A.

nlet rec nnzero (n:nnat 0 (dt ?)) : nnat 0 (dt ?) ≝
 match n return ? with
  [ nO ⇒ nO 0 (dt ?)
  | nS m _ ⇒ nmzero m ]
and nmzero (m:mat 0 (dt ?)) : nnat 0 (dt ?) ≝ 
 match m return ? with
 [ mS n ⇒ nnzero n ].

nrecord pair (n: nat) (x: DT n) (label: Type): Type ≝
 { lbl:label; l: pair n x label; r: pair n x label}.
