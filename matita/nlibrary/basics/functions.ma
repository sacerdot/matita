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

include "Plogic/equality.ma".
include "Plogic/connectives.ma".

ndefinition compose ≝
  λA,B,C:Type.λf:B→C.λg:A→B.λx:A.
  f (g x).

interpretation "function composition" 'compose f g = (compose ? ? ? f g).

ndefinition injective: ∀A,B:Type[0].∀ f:A→B.Prop
≝ λA,B.λf.∀x,y:A.f x = f y → x=y.

ndefinition surjective: ∀A,B:Type[0].∀f:A→B.Prop
≝λA,B.λf.∀z:B.∃x:A.z = f x.

ndefinition symmetric: ∀A:Type[0].∀f:A→A→A.Prop 
≝ λA.λf.∀x,y.f x y = f y x.

ndefinition symmetric2: ∀A,B:Type[0].∀f:A→A→B.Prop
≝ λA,B.λf.∀x,y.f x y = f y x.

ndefinition associative: ∀A:Type[0].∀f:A→A→A.Prop
≝ λA.λf.∀x,y,z.f (f x y) z = f x (f y z).

(*
ntheorem eq_f_g_h:
  ∀A,B,C,D:Type[0].∀f:C→D.∀g:B→C.∀h:A→B.
  f∘(g∘h) = (f∘g)∘h.
  //.
nqed. *)

(* functions and relations *)
ndefinition monotonic : ∀A:Type.∀R:A→A→Prop.
∀f:A→A.Prop ≝
λA.λR.λf.∀x,y:A.R x y → R (f x) (f y).

(* functions and functions *)
ndefinition distributive: ∀A:Type[0].∀f,g:A→A→A.Prop
≝ λA.λf,g.∀x,y,z:A. f x (g y z) = g (f x y) (f x z).

ndefinition distributive2: ∀A,B:Type[0].∀f:A→B→B.∀g:B→B→B.Prop
≝ λA,B.λf,g.∀x:A.∀y,z:B. f x (g y z) = g (f x y) (f x z).

nlemma injective_compose : ∀A,B,C,f,g.
injective A B f → injective B C g → injective A C (λx.g (f x)).
/3/.
nqed.