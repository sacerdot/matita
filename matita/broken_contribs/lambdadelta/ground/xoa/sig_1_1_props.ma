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

include "basics/pts.ma".
include "basics/core_notation/imply_2.ma".

(* LOGIC ********************************************************************)

(* Weak sigma type (1, 1) ***************************************************)

record sig (A:Type[0]) (f:A→Prop) : Type[0] ≝
  { sig_a: A        (* car *)
  ; sig_d: f sig_a  (* cdr *)
  }
.

interpretation
  "weak sigma type (1, 1)"
  'sigma x = (sig ? x).

(*
interpretation "mk_Sig" 'dp x y = (mk_Sig ?? x y).

lemma sub_pi2 : ∀A.∀P,P':A → Prop. (∀x.P x → P' x) → ∀x:Σx:A.P x. P' (pi1 … x).
#A #P #P' #H1 * #x #H2 @H1 @H2
qed.

lemma inj_mk_Sig: ∀A,P.∀x. x = mk_Sig A P (pi1 A P x) (pi2 A P x).
#A #P #x cases x //
qed-.
*)
