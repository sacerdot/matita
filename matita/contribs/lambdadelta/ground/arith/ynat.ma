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

include "ground/arith/pnat.ma".
include "ground/notation/functions/zero_0.ma".
include "ground/notation/functions/infinity_0.ma".

(* NON-NEGATIVE INTEGERS WITH INFINITY **************************************)

(*** ynat *)
inductive ynat: Type[0] ≝
| yzero: ynat
| yinj : pnat → ynat
| yinf : ynat
.

coercion yinj.

interpretation
  "zero (non-negative integers with infinity)"
  'Zero = yzero.

interpretation
  "infinity (non-negative integers with infinity)"
  'Infinity = yinf.

(* Inversion lemmas *********************************************************)

(* Note: destruct *)
(*** yinj_inj *)
lemma eq_inv_yinj_bi (y1) (y2): yinj y1 = yinj y2 → y1 = y2.
#x #y #H destruct //
qed-.

(* Basic properties *********************************************************)

(*** eq_ynat_dec *)
lemma eq_ynat_dec (y1,y2:ynat): Decidable (y1 = y2).
* [| #p1 |] *
[1,9: /2 width=1 by or_introl/ |2,5,8: #p2 ]
[2: elim (eq_pnat_dec p1 p2)
    /4 width=1 by eq_inv_yinj_bi, or_intror, or_introl/
|*: @or_intror #H destruct
]
qed-.
