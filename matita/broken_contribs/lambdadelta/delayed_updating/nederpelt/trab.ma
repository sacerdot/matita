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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/white_righttriangle_b_5.ma".
include "ground/arith/nat_pred.ma".
include "ground/arith/nat_succ.ma".

(* BALANCED SEGMENT TRAVERSING **********************************************)

definition trab_k (S:Type[0]): Type[0] ≝ path → nat → path → S.

rec definition trab (S:Type[0]) (K:trab_k S) (p) (n) (q) on p : S ≝
match p with
[ list_empty     ⇒ K p n q
| list_lcons l x ⇒
  match l with
  [ label_d k ⇒ trab S K x n (𝗱k◗q)
  | label_m   ⇒ trab S K x n (𝗺◗q)
  | label_L   ⇒ trab S K x (↑n) (𝗟◗q)
  | label_A   ⇒
    match n with
    [ nzero  ⇒ K p n q
    | ninj y ⇒ trab S K x (pnpred y) (𝗔◗q)
    ]
  | label_S   ⇒ trab S K x n (𝗦◗q)
  ]
].

interpretation
  "balanced segment traversing (path)"
  'WhiteRightTriangleB S K p n q = (trab S K p n q).
