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

include "logic/equality.ma".

inductive unit (A : Type) (a : A) : Type := mk_unit : unit A a.

definition k : ∀A,a.unit A a → A := λA,a.λx:unit A a.a.
coercion k.

record monoid : Type := {
  mC :> Type;
  mOp : mC -> mC -> mC;
  m1 : mC;
  mP : ∀x:mC.x = mOp x m1
}. 

record group : Type := {
  gC :> Type;
  gOp : gC -> gC -> gC;
  gInv : gC -> gC;
  g1 : gC;
  gP : ∀x:gC.gOp x (gInv x) = g1 
}.

(*
record monoid_aux (x : Type) : Type := {
  xC :> unit ? x;
  xOp : let xC := k ?? xC in xC -> xC -> xC;
  x1  : let xC := k ?? xC in xC;
  xP  : let xC := k ?? xC in ∀x:xC. x = xOp x x1
}.
*)

record monoid_aux (xC : Type) : Type := {
  (*xC :> unit ? x;*)
  xOp : (*let xC := k ?? xC in*) xC -> xC -> xC;
  x1  : (*let xC := k ?? xC in*) xC;
  xP  : (*let xC := k ?? xC in*) ∀x:xC. x = xOp x x1
}.


definition m_sub := λT:Type.λx:monoid_aux T.
  mk_monoid (*k ?? (xC T x)*) T (xOp ? x) (x1 ? x) (xP ? x).
coercion m_sub.

lemma test : ∀G:group.∀M:monoid_aux (gC G).gC G = mC (m_sub ? M).
intros; reflexivity;
qed.

record ring : Type := {
  rG :> group;
  rM :> monoid_aux (gC rG);
  rP : ∀x,y,z:rG. mOp rM x (gOp rG y z) = gOp rG (mOp rM x y) (mOp rM x z)
}.

lemma prova : ∀R:ring.∀x:R. x = mOp R x (m1 R).
intros;
apply (mP (rM R));
qed.

include "Z/times.ma".

lemma e_g : group.
constructor 1; 
[ apply Z;
| apply Zplus;
| apply (λx.-x);
| apply OZ;
| intros; autobatch;]
qed.

lemma e_m : monoid.
constructor 1;
[ apply Z;
| apply Ztimes;
| apply (pos O);
| intros; autobatch;]
qed.

lemma em_1 : monoid_aux Z.
constructor 1;
[ apply Ztimes;
| apply (pos O);
| intros; autobatch;]
qed.

lemma e_r : ring.
constructor 1;
[ apply e_g; | apply em_1;| intros; unfold e_g; unfold em_1; simplify; autobatch;]
qed.

lemma test1 : ∀x:Z.x = x * pos O.
intros; apply (mP e_r x);
qed.
  


 
