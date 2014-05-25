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

include "basic_2/substitution/llpx_sn_ldrop.ma".
include "basic_2/static/ssta.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS ******************************)

(* Properties on lazy sn pointwise extensions *******************************)

lemma ssta_llpx_sn_conf: ∀R. (∀I,L.reflexive … (R I L)) →
                             (∀I.l_liftable (R I)) →
                         ∀h,g,G. s_r_confluent1 … (ssta h g G) (llpx_sn R 0).
#R #H1R #H2R #h #g #G #Ls #T1 #T2 #H elim H -G -Ls -T1 -T2
[ /3 width=4 by llpx_sn_fwd_length, llpx_sn_sort/
| #G #Ls #Ks #V1s #W2s #V2s #i #HLKs #_ #HVW2s #IHV12s #Ld #H elim (llpx_sn_inv_lref_ge_sn … H … HLKs) // -H
  #Kd #V1d #HLKd #HV1s #HV1sd
  lapply (ldrop_fwd_drop2 … HLKs) -HLKs #HLKs
  lapply (ldrop_fwd_drop2 … HLKd) -HLKd #HLKd
  @(llpx_sn_lift_le … HLKs HLKd … HVW2s) -HLKs -HLKd -HVW2s /2 width=1 by/ (**) (* full auto too slow *)
| #G #Ls #Ks #V1s #W1s #l #i #HLKs #Hl #HVW1s #Ld #H elim (llpx_sn_inv_lref_ge_sn … H … HLKs) // -H
  #Kd #V1d #HLKd #HV1s #HV1sd
  lapply (ldrop_fwd_drop2 … HLKs) -HLKs #HLKs
  lapply (ldrop_fwd_drop2 … HLKd) -HLKd #HLKd
  @(llpx_sn_lift_le … HLKs HLKd … HVW1s) -HLKs -HLKd -HVW1s /2 width=1 by/ (**) (* full auto too slow *)
| #a #I #G #Ls #V #T1 #T2 #_ #IHT12 #Ld #H elim (llpx_sn_inv_bind_O … H) -H
  /4 width=5 by llpx_sn_bind_repl_SO, llpx_sn_bind/
| #G #Ls #V #T1 #T2 #_ #IHT12 #Ld #H elim (llpx_sn_inv_flat … H) -H
  /3 width=1 by llpx_sn_flat/
| #G #Ls #V #T1 #T2 #_ #IHT12 #Ld #H elim (llpx_sn_inv_flat … H) -H
  /3 width=1 by llpx_sn_flat/
]
qed-.
