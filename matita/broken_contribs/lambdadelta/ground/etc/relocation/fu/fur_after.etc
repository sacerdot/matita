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

include "ground/relocation/fu/fur_nexts.ma".
include "ground/notation/functions/compose_3.ma".
include "ground/notation/functions/compose_2.ma".

(* COMPOSITION FOR FINITE RELOCATION MAPS FOR UNWIND ************************)

rec definition fur_after_aux (h: 𝔽𝕌→𝔽𝕌→𝔽𝕌) (g:𝔽𝕌) (f:𝔽𝕌) on f: 𝔽𝕌.
cases f -f [| #i #f cases i -i [| #k ]]
[ @(⫯g)
| @(⫯(h g f))
| @(⮤*[k](fur_after_aux h g f))
]
defined.

interpretation
  "auxiliary composition (finite relocation maps for unwind)"
  'Compose f f2 f1 = (fur_after_aux f f2 f1).

rec definition fur_after (g:𝔽𝕌) (f:𝔽𝕌) on g: 𝔽𝕌.
cases g [| #i #g cases i -i [| #k ]]
[ @f
| @(g•[fur_after]f)
| @(fur_after g (↑*[k]f))
]
defined.

interpretation
  "composition (finite relocation maps for unwind)"
  'Compose f2 f1 = (fur_after f2 f1).

(* Basic constructions ******************************************************)

lemma fur_after_aux_id_dx (h) (g):
      (⫯g) = g•[h]𝐢.
// qed.

lemma fur_after_aux_p_dx (h) (g) (f):
      (⫯(h g f)) = g•[h](⫯f).
// qed.

lemma fur_after_aux_j_dx (h) (g) (f) (n):
      (⮤*[n](g•[h]f)) = g•[h](⮤*[n]f).
// qed.

lemma fur_after_id_sn (f):
      f = 𝐢•f.
// qed.

lemma fur_after_p_sn (g) (f):
      g•[fur_after]f = (⫯g)•f.
// qed.

lemma fur_after_p_id (g):
      (⫯g) = (⫯g)•𝐢.
// qed.

lemma fur_after_p_bi (g) (f):
      (⫯(g•f)) = (⫯g)•(⫯f).
// qed.

lemma fur_after_p_j (g) (f) (n):
      (⮤*[n]((⫯g)•f)) = (⫯g)•(⮤*[n]f).
// qed.

lemma fur_after_j_sn (g) (f) (n):
      g•(↑*[n]f) = (⮤*[n]g)•f.
// qed.
