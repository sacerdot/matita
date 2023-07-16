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
include "ground/relocation/fu/fur_minus_pushs.ma".

(* RIGHT SUBTRACTION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

(* Constructions with fur_nexts *********************************************)

lemma fur_minus_nexts_push (f) (k) (r):
      ↑*[k](f-r) = (↑*[k]f)-⫯r.
#f #k #r
<fur_nexts_unfold <fur_nexts_unfold
>fur_minus_pushs_sn //
qed.

lemma fur_minus_nexts_next (f) (k) (r):
      ↑*[𝟎]⫯*[k](f-r) = (↑*[k]f)-↑r.
#f #k #r
>fur_minus_pushs_sn //
qed.

