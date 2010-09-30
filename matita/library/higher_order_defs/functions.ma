(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "logic/equality.ma".

definition compose \def
  \lambda A,B,C:Type.\lambda f:(B\to C).\lambda g:(A\to B).\lambda x:A.
  f (g x).

interpretation "function composition" 'compose f g = (compose ? ? ? f g).

definition injective: \forall A,B:Type.\forall f:A \to B.Prop
\def \lambda A,B.\lambda f.
  \forall x,y:A.f x = f y \to x=y.

definition surjective: \forall A,B:Type.\forall f:A \to B.Prop
\def \lambda A,B.\lambda f.
  \forall z:B. \exists x:A.z=f x.

definition symmetric: \forall A:Type.\forall f:A \to A\to A.Prop
\def \lambda A.\lambda f.\forall x,y.f x y = f y x.

definition symmetric2: \forall A,B:Type.\forall f:A \to A\to B.Prop
\def \lambda A,B.\lambda f.\forall x,y.f x y = f y x.

definition associative: \forall A:Type.\forall f:A \to A\to A.Prop
\def \lambda A.\lambda f.\forall x,y,z.f (f x y) z = f x (f y z).

theorem eq_f_g_h:
  \forall A,B,C,D:Type.
  \forall f:C \to D.\forall g:B \to C.\forall h:A \to B.
  f \circ (g \circ h) = (f \circ g) \circ h.
  intros.
  reflexivity.
qed.

(* functions and relations *)
definition monotonic : \forall A:Type.\forall R:A \to A \to Prop.
\forall f:A \to A.Prop \def
\lambda A. \lambda R. \lambda f. \forall x,y:A.R x y \to R (f x) (f y).

(* functions and functions *)
definition distributive: \forall A:Type.\forall f,g:A \to A \to A.Prop
\def \lambda A.\lambda f,g.\forall x,y,z:A. f x (g y z) = g (f x y) (f x z).

definition distributive2: \forall A,B:Type.\forall f:A \to B \to B.
\forall g: B\to B\to B. Prop
\def \lambda A,B.\lambda f,g.\forall x:A.\forall y,z:B. f x (g y z) = g (f x y) (f x z).

lemma injective_compose : ∀A,B,C,f,g.injective A B f → injective B C g → 
  injective A C (λx.g (f x)).
intros;unfold;intros;simplify in H2;apply H;apply H1;assumption;
qed.