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

include "static_2/static/feqg_fqup.ma".
include "basic_2/rt_transition/fpbc_feqg.ma".
include "basic_2/rt_computation/fsb.ma".

(* STRONGLY NORMALIZING CLOSURES FOR PARALLEL RST-TRANSITION ****************)

(* Properties with generic equivalence for closures *************************)

lemma fsb_feqg_trans (S):
      reflexive … S → symmetric … S → Transitive … S →
      ∀G1,L1,T1. ≥𝐒 ❨G1,L1,T1❩ →
      ∀G2,L2,T2. ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩ → ≥𝐒 ❨G2,L2,T2❩.
#S #H1S #H2S #H3S #G1 #L1 #T1 #H @(fsb_ind … H) -G1 -L1 -T1
#G1 #L1 #T1 #_ #IH #G2 #L2 #T2 #H12
@fsb_intro #G #L #T #H2
elim (feqg_fpbc_trans … H12 … H2) -G2 -L2 -T2
/4 width=5 by fpbc_intro, feqg_refl/
qed-.
