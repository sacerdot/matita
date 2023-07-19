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

include "delayed_updating/substitution/lift_rmap.ma".
include "delayed_updating/substitution/prelift_rmap_eq.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Constructions with trz_eq ************************************************)

lemma lift_rmap_eq_repl (p):
      compatible_2_fwd … trz_eq trz_eq (λf.🠢[f]p).
#p elim p -p //
#l #p #IH #f1 #f2 #Hf
/3 width=1 by prelift_rmap_eq_repl/
qed.

lemma tls_lift_rmap_d_dx (f) (p) (n) (k):
      (⫰*[n+k]🠢[f]p) ≐ ⫰*[n]🠢[f](p◖𝗱k).
// qed.
