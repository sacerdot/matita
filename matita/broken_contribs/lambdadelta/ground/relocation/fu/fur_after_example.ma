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

include "ground/relocation/fu/fur_after.ma".
include "ground/arith/pnat_two.ma".
include "ground/arith/pnat_three.ma".

(* COMPOSITION FOR FINITE RELOCATION MAPS FOR UNWIND ************************)

(* Examples *****************************************************************)

lemma fur_after_example_0123_invalid:
      (⮤*[𝟎]⮤*[⁤𝟐]⫯↑*[⁤𝟏]⮤*[⁤𝟑]𝐢) = (⮤*[𝟎]⫯⮤*[⁤𝟏]𝐢)•(⮤*[⁤𝟐]⫯⮤*[⁤𝟑]𝐢).
<fur_after_j_sn <fur_after_p_sn <fur_after_aux_j_dx
<fur_after_aux_j_dx
<fur_after_aux_p_dx
<fur_after_j_sn <fur_after_id_sn
//
qed.

lemma fur_after_example_1302_valid:
      (⮤*[𝟎]⫯⮤*[⁤𝟏]⫯⫯⮤*[⁤𝟐]⫯⮤*[⁤𝟑]𝐢) = (⫯⮤*[⁤𝟏]⫯⫯⫯⮤*[⁤𝟑]𝐢)•(⮤*[𝟎]⫯⫯⮤*[⁤𝟐]𝐢).
<fur_after_p_sn
<fur_after_aux_j_dx <fur_after_aux_p_dx
<fur_after_j_sn <fur_after_p_sn
<fur_after_aux_j_dx <fur_after_aux_p_dx
<fur_after_p_sn <fur_after_aux_p_dx
<fur_after_p_sn
<fur_after_aux_j_dx <fur_after_aux_id_dx
//
qed.
(*
lemma fur_after_example_0123:
      (⮤*[⁤𝟐]⫯↑*[⁤𝟑]⫯⮤*[𝟎]⫯⮤*[⁤𝟏]𝐢) = (⮤*[⁤𝟐]⫯⮤*[⁤𝟑]𝐢)•(⮤*[𝟎]⫯⮤*[⁤𝟏]𝐢).
<fur_after_j_sn <fur_after_p_sn <fur_after_aux_j_dx
<fur_after_aux_p_dx <piter_unit
<fur_after_j_sn <fur_after_id_sn
//
qed.

lemma fur_after_example_0000:
      (⮤*[𝟎]⮤*[𝟎]⫯↑*[𝟎]⮤*[𝟎]𝐢) = (⮤*[𝟎]⫯⮤*[𝟎]𝐢)•(⮤*[𝟎]⫯⮤*[𝟎]𝐢).
<fur_after_j_sn <fur_after_p_sn <fur_after_aux_j_dx
<fur_after_aux_j_dx <fur_after_aux_p_dx
<fur_after_j_sn <fur_after_id_sn
//
qed.
*)