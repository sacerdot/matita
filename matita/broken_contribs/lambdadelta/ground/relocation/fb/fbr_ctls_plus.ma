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

include "ground/relocation/fb/fbr_ctls.ma".
include "ground/arith/nat_plus.ma".

(* ITERATED COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS ************)

(* Constructions with nplus *************************************************)

lemma fbr_ctls_plus (f) (m) (n):
      (⫰*[n]⫰*[m]f) = ⫰*[m+n]f.
#f #m #n @(niter_plus … (λf.⫰f))
qed.
