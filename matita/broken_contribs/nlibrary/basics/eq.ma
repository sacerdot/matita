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

include "basics/relations.ma".

interpretation "leibnitz's non-equality" 'neq t x y = (Not (eq t x y)).

(* this is refl 
ntheorem reflexive_eq : ∀A:Type. reflexive A (eq A).
//; nqed. *)

(* this is sym_eq 
ntheorem symmetric_eq: ∀A:Type. symmetric A (eq A).
//; nqed. *)

ntheorem transitive_eq : ∀A:Type. transitive A (eq A).
#A; #x; #y; #z; #H1; #H2; nrewrite > H1; //; nqed.

(*
ntheorem symmetric_not_eq: ∀A:Type. symmetric A (λx,y.x ≠ y).
/3/; nqed.
*)

ntheorem symmetric_not_eq: ∀A:Type. ∀x,y:A. x ≠ y → y ≠ x.
/3/; nqed.

(*
#A; #x; #y; #H; #K; napply H; napply symmetric_eq; //; nqed.
*)

ntheorem eq_f: ∀A,B:Type.∀f:A→B.∀x,y:A. x=y → f x = f y.
#A; #B; #f; #x; #y; #H; nrewrite > H; //; nqed.

(*
theorem eq_f': \forall  A,B:Type.\forall f:A\to B.
\forall x,y:A. x=y \to f y = f x.
intros.elim H.apply refl_eq.
qed. *)

(* deleterio per auto*)
ntheorem eq_f2: ∀A,B,C:Type.∀f:A→B→C.
∀x1,x2:A.∀y1,y2:B. x1=x2 → y1=y2 → f x1 y1 = f x2 y2.
#A; #B; #C; #f; #x1; #x2; #y1; #y2; #E1; #E2; nrewrite > E1; nrewrite > E2;//.
nqed. 