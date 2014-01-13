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

include "basic_2/computation/lpxs_lleq.ma".
include "basic_2/computation/csx_alt.ma".
include "basic_2/computation/lsx_lpxs.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced forward lemmas **************************************************)
(*
lemma lsx_fwd_bind_dx_lpxs: ∀h,g,a,I,G,L1,V. ⦃G, L1⦄ ⊢ ⬊*[h, g] V →
                            ∀L2,T. G ⊢ ⋕⬊*[h, g, ⓑ{a,I}V.T] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                            G ⊢ ⋕⬊*[h, g, T] L2.ⓑ{I}V.
#h #g #a #I #G #L1 #V #H @(csx_ind_alt … H) -V
#V1 #_ #IHV1 #L2 #T #H @(lsx_ind … H) -L2
#L2 #HL2 #IHL2 #HL12 @lsx_intro
#Y #H #HnT elim (lpxs_inv_pair1 … H) -H
#L3 #V3 #HL23 #HV13 #H destruct
lapply (lpxs_trans … HL12 … HL23) #HL13
elim (eq_term_dec V1 V3)
[ -HV13 -HL2 -IHV1 -HL12 #H destruct
  @IHL2 -IHL2 // -HL23 -HL13 /3 width=2 by lleq_fwd_bind_O/
| -IHL2 -HL23 -HnT #HnV13
  @(IHV1 … HnV13) -IHV1 -HnV13 /2 width=3 by lpxs_cpxs_trans/ -HL12 -HL13 -HV13
  @(lsx_lpxs_trans) … HL2)
*)

(* Advanced inversion lemmas ************************************************)



(* Main properties **********************************************************)

axiom csx_lsx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → G ⊢ ⋕⬊*[h, g, T] L.
(*
#h #g #G #L #T @(fqup_wf_ind_eq … G L T) -G -L -T
#G1 #L1 #T1 #IH #G2 #L2 * *
[ #k #HG #HL #HT destruct //
| #i #HG #HL #HT destruct
  #H
| #p #HG #HL #HT destruct //
| #a #I #V2 #T2 #HG #HL #HT #H destruct
  elim (csx_fwd_bind … H) -H
  #HV2 #HT2
| #I #V2 #T2 #HG #HL #HT #H destruct
  elim (csx_fwd_flat … H) -H /3 width=1 by lsx_flat/
*)
