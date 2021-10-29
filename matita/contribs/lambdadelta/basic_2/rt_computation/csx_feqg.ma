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

include "static_2/static/feqg.ma".
include "basic_2/rt_computation/csx_reqg.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Properties with generic equivalence for closures *************************)

lemma csx_feqg_conf (S):
      reflexive … S → symmetric … S →
      ∀G1,L1,T1. ❨G1,L1❩ ⊢ ⬈*𝐒 T1 →
      ∀G2,L2,T2. ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩ → ❨G2,L2❩ ⊢ ⬈*𝐒 T2.
#S #H1S #H2S #G1 #L1 #T1 #HT1 #G2 #L2 #T2 * -G2 -L2 -T2
/3 width=6 by csx_reqg_conf, csx_teqg_trans/
qed-.
