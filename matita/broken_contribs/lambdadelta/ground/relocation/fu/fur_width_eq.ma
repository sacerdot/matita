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

include "ground/relocation/fu/fur_height.ma".
include "ground/relocation/fu/fur_eq.ma".

(* HEIGHT FOR FINITE RELOCATION MAPS FOR UNWIND *****************************)

(* Constructions with fur_eq ************************************************)
(*
lemma pippo (g1) (f2):
            (⮤*[⁤𝟏]g1) ≐ f2 →
            ∨∨ ∃∃g2. (⮤*[⁤𝟏]g1) ≐ g2 & f2 = ⮤*[𝟎]g2
             | ∃∃k,g2. g1 ≐ ⮤*[k]g2 & f2 = ⮤*[⁤↑k]g2
.
#g1 * [| * [| #k2 ] #f2 ]
[ #H0
  lapply (H0 (𝟏)) -H0 <fur_dapp_j_dx #H0
  lapply (fur_dapp_le g1 (𝟏+⁤𝟏)) >H0 -H0 #H0
  elim (plt_ge_false … H0) -H0 //
| #H0
  lapply (H0 (𝟏)) -H0 <fur_dapp_j_dx #H0
  lapply (fur_dapp_le g1 (𝟏+⁤𝟏)) >H0 -H0 #H0
  elim (plt_ge_false … H0) -H0 //
| @(nat_ind_succ … k2) -k2 [| #k2 #_ ] #H0
  [ /3 width=3 by ex2_intro, or_introl/
  | @or_intror @(ex2_2_intro … (k2) f2) //
    #p <fur_dapp_j_dx  /2 width=4 by _/
*)
lemma fur_height_eq_repl:
      compatible_2_fwd … fur_eq (eq …) (λf.♯f).
#f1 elim f1 -f1
[| * [| #k1 ] #f1 #IH ] #f2 #Hf
[ @(fur_eq_ind_id_sn … Hf) -f2 //
| @(fur_eq_ind_push_sn … Hf) -f2 /2 width=1 by/
  #f2 #Hf <fur_height_p_dx <fur_height_p_dx /2 width=1 by/
| <fur_height_j_dx
  lapply (Hf (𝟏)) <fur_dapp_j_dx #H0 