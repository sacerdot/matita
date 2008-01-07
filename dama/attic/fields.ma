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



include "attic/rings.ma".

record is_field (R:ring) (inv:∀x:R.x ≠ 0 → R) : Prop
≝
 {  (* multiplicative abelian properties *)
    mult_comm_: symmetric ? (mult R);
    (* multiplicative group properties *)
    inv_inverse_: ∀x.∀p: x ≠ 0. inv x p * x = 1
 }.

lemma opp_opp: ∀R:ring. ∀x:R. --x=x.
intros; 
apply (cancellationlaw ? (-x) ? ?); 
rewrite > (opp_inverse R x); 
rewrite > plus_comm;
rewrite > opp_inverse;
reflexivity.
qed.

let rec sum (C:Type) (plus:C→C→C) (zero,one:C) (n:nat) on n  ≝
 match n with
  [ O ⇒ zero
  | (S m) ⇒ plus one (sum C plus zero one m)
  ].

record field : Type \def
 { f_ring:> ring;
   inv: ∀x:f_ring. x ≠ 0 → f_ring;
   field_properties: is_field f_ring inv
 }.
 
theorem mult_comm: ∀F:field.symmetric ? (mult F).
 intro;
 apply (mult_comm_ ? ? (field_properties F)).
qed.

theorem inv_inverse: ∀F:field.∀x:F.∀p: x ≠ 0. (inv ? x p)*x = 1.
 intro;
 apply (inv_inverse_ ? ? (field_properties F)).
qed.

(*CSC: qua funzionava anche mettendo ? al posto della prima F*)
definition sum_field ≝
 λF:field. sum F (plus F) 0 1.
