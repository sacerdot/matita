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

include "ground/relocation/fb/fbr_rconss.ma".
include "ground/arith/nat_plus.ma".

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with nplus *************************************************)

lemma fbr_rconss_plus (b) (f) (m) (n):
      (f◖*[m]b)◖*[n]b = f◖*[m+n]b.
#b #f #m #n @(niter_plus … (λf.f◖b))
qed.
