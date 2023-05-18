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
include "ground/arith/nat_pred_succ.ma".

(* BALANCED SEGMENT TRAVERSAL ***********************************************)

definition trab_k (S:Type[0]): Type[0] ≝ path → ℕ → path → S.

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
    | npos y ⇒ trab S K x (pnpred y) (𝗔◗q)
    ]
  | label_S   ⇒ K p n q
  ]
].

interpretation
  "balanced segment traversing (path)"
  'WhiteRightTriangleB S K p n q = (trab S K p n q).

(* Basic destructions *******************************************************)

lemma trab_unfold_empty (S) (K) (q) (n):
      K (𝐞) n q = ▷𝐛{S}[K]❨𝐞,n,q❩.
// qed.

lemma trab_unfold_d (S) (K) (p) (q) (n) (k):
      ▷𝐛{S}[K]❨p,n,𝗱k◗q❩ = ▷𝐛{S}[K]❨p◖𝗱k,n,q❩.
// qed.

lemma trab_unfold_m (S) (K) (p) (q) (n):
      ▷𝐛{S}[K]❨p,n,𝗺◗q❩ = ▷𝐛{S}[K]❨p◖𝗺,n,q❩.
// qed.

lemma trab_unfold_L (S) (K) (p) (q) (n):
      ▷𝐛{S}[K]❨p,↑n,𝗟◗q❩ = ▷𝐛{S}[K]❨p◖𝗟,n,q❩.
// qed.

lemma trab_unfold_A_zero (S) (K) (p) (q):
      K (p◖𝗔) (𝟎) q = ▷𝐛{S}[K]❨p◖𝗔,𝟎,q❩.
// qed.

lemma trab_unfold_A_inj (S) (K) (p) (q) (k:ℤ⁺):
      ▷𝐛{S}[K]❨p,↓k,𝗔◗q❩ = ▷𝐛{S}[K]❨p◖𝗔,k,q❩.
// qed.

lemma trab_unfold_S (S) (K) (p) (q) (n):
      K (p◖𝗦) n q = ▷𝐛{S}[K]❨p◖𝗦,n,q❩.
// qed.

(* Advanced destructions *******************************************)

lemma trab_unfold_A_succ (S) (K) (p) (q) (n):
      ▷𝐛{S}[K]❨p,n,𝗔◗q❩ = ▷𝐛{S}[K]❨p◖𝗔,↑n,q❩.
// qed.
