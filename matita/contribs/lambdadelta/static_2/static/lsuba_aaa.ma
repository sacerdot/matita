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

include "static_2/static/aaa_aaa.ma".
include "static_2/static/lsuba.ma".

(* RESTRICTED REFINEMENT FOR ATOMIC ARITY ASSIGNMENT ************************)

(* Properties with atomic arity assignment **********************************)

lemma lsuba_aaa_conf: ∀G,L1,V,A. ⦃G,L1⦄ ⊢ V ⁝ A →
                      ∀L2. G ⊢ L1 ⫃⁝ L2 → ⦃G,L2⦄ ⊢ V ⁝ A.
#G #L1 #V #A #H elim H -G -L1 -V -A
[ //
| #I #G #L1 #V #A #HA #IH #L2 #H
  elim (lsuba_inv_bind1 … H) -H * /3 width=1 by aaa_zero/
  #L0 #W0 #V0 #A0 #HV0 #HW0 #HL10 #H1 #H2 destruct
  lapply (aaa_mono … HV0 … HA) #H destruct -V0 -L1 /2 width=1 by aaa_zero/
| #I #G #K1 #A #i #_ #IH #L2 #H
  elim (lsuba_inv_bind1 … H) -H * /3 width=1 by aaa_lref/
| /4 width=2 by lsuba_bind, aaa_abbr/
| /4 width=1 by lsuba_bind, aaa_abst/
| /3 width=3 by aaa_appl/
| /3 width=1 by aaa_cast/
]
qed-.

lemma lsuba_aaa_trans: ∀G,L2,V,A. ⦃G,L2⦄ ⊢ V ⁝ A →
                       ∀L1. G ⊢ L1 ⫃⁝ L2 → ⦃G,L1⦄ ⊢ V ⁝ A.
#G #L2 #V #A #H elim H -G -L2 -V -A
[ //
| #I #G #L2 #V #A #HA #IH #L1 #H
  elim (lsuba_inv_bind2 … H) -H * /3 width=1 by aaa_zero/
  #L0 #V0 #W0 #A0 #HV0 #HW0 #HL02 #H1 #H2 destruct
  lapply (aaa_mono … HW0 … HA) #H destruct -L2 /2 width=1 by aaa_zero/
| #I #G #K2 #A #i #_ #IH #L1 #H
  elim (lsuba_inv_bind2 … H) -H * /3 width=1 by aaa_lref/
| /4 width=2 by lsuba_bind, aaa_abbr/
| /4 width=1 by lsuba_bind, aaa_abst/
| /3 width=3 by aaa_appl/
| /3 width=1 by aaa_cast/
]
qed-.
