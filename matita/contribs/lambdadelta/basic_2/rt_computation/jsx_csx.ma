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

include "basic_2/rt_computation/rsx_csx.ma".
include "basic_2/rt_computation/jsx_drops.ma".
include "basic_2/rt_computation/jsx_lsubr.ma".

(* COMPATIBILITY OF STRONG NORMALIZATION FOR UNBOUND RT-TRANSITION **********)

(* Properties with strongly rt-normalizing terms ****************************)

lemma jsx_csx_conf (h) (G):
      ∀L1,L2. G ⊢ L1 ⊒[h] L2 →
      ∀T. ⦃G,L1⦄ ⊢ ⬈*[h] 𝐒⦃T⦄ → ⦃G,L2⦄ ⊢ ⬈*[h] 𝐒⦃T⦄.
/3 width=5 by jsx_fwd_lsubr, csx_lsubr_conf/ qed-.

(* Properties with strongly rt-normalizing referred local environments ******)

(* Note: Try by induction on the 2nd premise by generalizing V with f *) 
lemma rsx_jsx_trans (h) (G):
      ∀L1,V. G ⊢ ⬈*[h,V] 𝐒⦃L1⦄ →
      ∀L2. G ⊢ L1 ⊒[h] L2 → G ⊢ ⬈*[h,V] 𝐒⦃L2⦄.
#h #G #L1 #V @(fqup_wf_ind_eq (Ⓕ) … G L1 V) -G -L1 -V
#G0 #L0 #V0 #IH #G #L1 * *
[ //
| #i #HG #HL #HV #H #L2 #HL12 destruct
  elim (rsx_inv_lref_drops … H) -H [|*: * ]
  [ #HL1 -IH
    lapply (jsx_fwd_drops_atom_sn … HL12 … HL1) -L1
    /2 width=1 by rsx_lref_atom_drops/
  | #I #K1 #HLK1 -IH
    elim (jsx_fwd_drops_unit_sn … HL12 … HLK1) -L1 [| // ] #K2 #HK12 #HLK2
    /2 width=3 by rsx_lref_unit_drops/
  | #I #K1 #V1 #HLK1 #HV1 #HK1
    elim (jsx_fwd_drops_pair_sn … HL12 … HLK1) -HL12 [3: // |*: * ]
    [ #K2 #HK12 #HLK2
      /4 width=6 by rsx_lref_pair_drops, jsx_csx_conf, fqup_lref/
    | #K2 #_ #HLK2 #_
      /2 width=3 by rsx_lref_unit_drops/
    ]
  ]
| //
| #p #I #V #T #HG #HL #HV #H #L2 #HL12 destruct
  elim (rsx_inv_bind_void … H) -H #HV #HT
  /4 width=4 by jsx_bind, rsx_bind_void/
| #I #V #T #HG #HL #HV #H #L2 #HL12 destruct
  elim (rsx_inv_flat … H) -H #HV #HT
  /3 width=4 by rsx_flat/
]
qed-.
