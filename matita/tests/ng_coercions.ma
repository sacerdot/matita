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

(* easy *)
naxiom T : Type.
naxiom S : Type.
naxiom R : Type.
naxiom U : Type.
naxiom c : T → S.
naxiom c1 : S → R.
naxiom c2 : R → U.

ncoercion foo1 : ∀_t:T.S ≝ c on _t : T to S.
ncoercion foo2 : ∀_r:R.U ≝ c2 on _r : R to U.
ncoercion foo3 : ∀_s:S.R ≝ c1 on _s : S to R.

(* another *)

naxiom nat : Type.
naxiom A : nat → Type. 
naxiom B : nat → Type.
naxiom C : nat → Type.
naxiom D : nat → Type.
naxiom a :  ∀n:nat. A n → B n.
naxiom a1 : ∀n:nat. B n → C n.
naxiom a2 : ∀n:nat. C n → D n.

ncoercion foo1 : ∀n:nat. ∀_a:A n. B n ≝ a  on _a : A ? to B ?.
ncoercion foo2 : ∀n:nat. ∀_c:C n. D n ≝ a2 on _c : C ? to D ?.
ncoercion foo3 : ∀n:nat. ∀_b:B n. C n ≝ a1 on _b : B ? to C ?.

naxiom cx : ∀n,m:nat. B n → C m.

ncoercion foo3 : ∀n,m:nat. ∀_b:B n. C m ≝ cx on _b : B ? to C ?.

naxiom Suc : nat → nat.
naxiom cs : ∀n:nat. B n → C (Suc n).

ncoercion foo3 : ∀n:nat. ∀_b:B n. C (Suc n) ≝ cs on _b : B ? to C ?.

(* funclass *)
naxiom Y : Type.
naxiom W : Type.
naxiom X : Type.
naxiom f : Y → W.
naxiom g : W → X → X → X.

ncoercion foo : ∀_y:Y. W ≝ f on _y : Y to W. 
ncoercion foo : ∀_w:W. X → X → X ≝ g on _w : W to Π_.Π_.?.
