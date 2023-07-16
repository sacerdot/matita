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

include "ground/relocation/fu/fur_minus.ma".
include "ground/relocation/fu/fur_height.ma".
include "ground/relocation/fu/fur_after.ma".
include "ground/relocation/fb/fbr_width.ma".
include "ground/relocation/fb/fbr_pushs.ma".
include "ground/arith/nat_le.ma".

axiom fur_minus_pushs_dx_width (r) (f):
      f = f-⫯*[♯f]r.

(* RIGHT MINUS FOR FINITE RELOCATION MAPS FOR UNWIND ************************)

(* Constructions with fur_after *********************************************)

lemma fur_minus_after_aux (h) (f) (g) (r):
      (∀f,r. ↕r ≤ ♯f →  h g (f-r) = (h g f)-⫯*[♯g]r) →
      ↕r ≤ ♯f → g•[h](f-r) = (g•[h]f)-⫯*[♯g]r.
#h #f elim f -f
[ #g #r #_ #_
  <fur_minus_id_sn <fur_after_aux_id_dx //
| * [| #k ] #f #IH #g #r #Hh
  [ <fur_after_aux_p_dx <fur_after_aux_p_dx
    #Hr lapply (Hh f … Hr) -Hh -Hr #Hh //
  | <fur_after_aux_j_dx
    cases r -r [| * #r ] #Hr
    [
    | lapply (nle_inv_succ_bi … Hr) -Hr #Hr
      <fur_minus_join_next <fur_after_aux_j_dx
      >IH -IH /2 width=1 by/ 
     <fur_minus_join_next
     <IH //  
  
   -IH //
  
  
   <fur_height_j_dx
   <fur_minus_join_pos
  
  
]
qed.

lemma fur_minus_after (g) (f) (n):
      (g-(n-♯f))•(f-n) = (g•f)-n.
#g elim g -g //
* [| #k ] #g #IH #f #n
[ /2 width=1 by fur_minus_after_aux/
| <fur_after_j_sn <IH -IH <fur_height_nexts 
  cases n -n // #p
  <fur_minus_nexts_pos
  
