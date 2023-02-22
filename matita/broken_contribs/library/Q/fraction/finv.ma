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

include "Z/plus.ma".
include "Q/fraction/fraction.ma".

let rec finv f ≝                                               
  match f with
  [ pp n ⇒ nn n
  | nn n ⇒ pp n
  | cons x g ⇒ cons (Zopp x) (finv g)].

theorem finv_finv: ∀f. finv (finv f) = f.
 intro; 
 elim f;
  [1,2: reflexivity
  | simplify;
    rewrite > H;
    rewrite > Zopp_Zopp;
    reflexivity
  ]
qed.
