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

include "delayed_updating/syntax/label.ma".
include "delayed_updating/notation/functions/black_righttriangle_2.ma".
include "ground/relocation/tr_uni.ma".
include "ground/relocation/tr_compose.ma".

(* TAILED PREUNWIND FOR RELOCATION MAP **************************************)

definition preunwind2_rmap (f) (l): tr_map â
match l with
[ label_d k â fâğ®â¨kâ©
| label_m   â f
| label_L   â â«¯f
| label_A   â f
| label_S   â f
].

interpretation
  "tailed preunwind (relocation map)"
  'BlackRightTriangle f l = (preunwind2_rmap f l).

(* Basic constructions ******************************************************)

lemma preunwind2_rmap_d (f) (k:pnat):
      fâğ®â¨kâ© = â¶[f]ğ±k.
// qed.

lemma preunwind2_rmap_m (f):
      f = â¶[f]ğº.
// qed.

lemma preunwind2_rmap_L (f):
      (â«¯f) = â¶[f]ğ.
// qed.

lemma preunwind2_rmap_A (f):
      f = â¶[f]ğ.
// qed.

lemma preunwind2_rmap_S (f):
      f = â¶[f]ğ¦.
// qed.
