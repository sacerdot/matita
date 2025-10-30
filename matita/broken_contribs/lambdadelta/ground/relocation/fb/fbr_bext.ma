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

include "ground/relocation/fb/fbr_map.ma".
include "ground/notation/functions/element_bx_3.ma".

(* BOOLEAN EXTENSION FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************)

rec definition fbr_bext (f) (f1) (f2) on f1: 𝔽𝔹 ≝
match f1 with
[ list_empty       ⇒
  if f (ⓕ) (ⓣ) then f2 else f1
| list_lcons b1 g1 ⇒
  match f2 with
  [ list_empty       ⇒
    if f (ⓣ) (ⓕ) then f1 else f2
  | list_lcons b2 g2 ⇒
    (fbr_bext f g1 g2)◖(f b1 b2)
  ]
].

interpretation
  "boolean extension (finite relocation maps with booleans)"
  'ElementBX f f1 f2 = (fbr_bext f f1 f2).

(* Basic constructions ******************************************************)

lemma fbr_bext_id_bi (f):
      (𝐢) = 𝐛𝐱[f]❨𝐢,𝐢❩.
#f normalize
cases (f (ⓕ) (ⓣ)) //
qed.

lemma fbr_bext_id_sx_false (f) (f2):
      ⓕ = f (ⓕ) (ⓣ) →
      (𝐢) = 𝐛𝐱[f]❨𝐢,f2❩.
#f #f2 #H0
normalize <H0 -H0 //
qed.

lemma fbr_bext_id_sx_true (f) (f2):
      ⓣ = f (ⓕ) (ⓣ) →
      f2 = 𝐛𝐱[f]❨𝐢,f2❩.
#f #f2 #H0
normalize <H0 -H0 //
qed.

lemma fbr_bext_id_dx_false (f) (f1):
      ⓕ = f (ⓣ) (ⓕ) →
      (𝐢) = 𝐛𝐱[f]❨f1,𝐢❩.
#f *
[ #_ @fbr_bext_id_bi (**) (* auto fails *)
| #b1 #f1 #H0 normalize <H0 -H0 //
]
qed.

lemma fbr_bext_id_dx_true (f) (f1):
      ⓣ = f (ⓣ) (ⓕ) →
      f1 = 𝐛𝐱[f]❨f1,𝐢❩.
#f *
[ #_ @fbr_bext_id_bi (**) (* auto fails *)
| #b1 #f1 #H0 normalize <H0 -H0 //
]
qed.

lemma fbr_bext_rcons_bi (f) (f1) (f2) (b1) (b2):
      (𝐛𝐱[f]❨f1,f2❩◖(f b1 b2)) = 𝐛𝐱[f]❨f1◖b1,f2◖b2❩.
// qed.
