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

include "Q/q/q.ma".
include "Q/ratio/rinv.ma".

definition Qinv : Q → Q ≝
 λp.
  match p with
   [ OQ ⇒ OQ  (* arbitrary value *)
   | Qpos r ⇒ Qpos (rinv r)
   | Qneg r ⇒ Qneg (rinv r)
   ].

theorem Qinv_Qinv: ∀q. Qinv (Qinv q) = q.
 intro;
 elim q;
  [ reflexivity
  |*:simplify;
    rewrite > rinv_rinv;
    reflexivity]
qed.
