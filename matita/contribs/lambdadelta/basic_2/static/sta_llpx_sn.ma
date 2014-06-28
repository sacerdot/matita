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

include "basic_2/multiple/llpx_sn_drop.ma".
include "basic_2/static/sta.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS ******************************)

(* Properties on lazy sn pointwise extensions *******************************)

lemma sta_llpx_sn_conf: ∀R. (∀L. reflexive … (R L)) → l_liftable R →
                        ∀h,G. s_r_confluent1 … (sta h G) (llpx_sn R 0).
#R #H1R #H2R #h #G #Ls #T1 #T2 #H elim H -G -Ls -T1 -T2
[ /3 width=4 by llpx_sn_fwd_length, llpx_sn_sort/
| #G #Ls #Ks #V1s #W2s #V2s #i #HLKs #_ #HVW2s #IHV12s #Ld #H elim (llpx_sn_inv_lref_ge_sn … H … HLKs) // -H
  #Kd #V1d #HLKd #HV1s #HV1sd
  lapply (drop_fwd_drop2 … HLKs) -HLKs #HLKs
  lapply (drop_fwd_drop2 … HLKd) -HLKd #HLKd
  @(llpx_sn_lift_le … HLKs HLKd … HVW2s) -HLKs -HLKd -HVW2s /2 width=1 by/ (**) (* full auto too slow *)
| #G #Ls #Ks #V1s #W1s #V2s #i #HLKs #_ #HV12s #IHVW1s #Ld #H elim (llpx_sn_inv_lref_ge_sn … H … HLKs) // -H
  #Kd #V1d #HLKd #HV1s #HV1sd
  lapply (drop_fwd_drop2 … HLKs) -HLKs #HLKs
  lapply (drop_fwd_drop2 … HLKd) -HLKd #HLKd
  @(llpx_sn_lift_le … HLKs HLKd … HV12s) -HLKs -HLKd -HV12s /2 width=1 by/ (**) (* full auto too slow *)
| #a #I #G #Ls #V #T1 #T2 #_ #IHT12 #Ld #H elim (llpx_sn_inv_bind_O … H) -H
  /4 width=5 by llpx_sn_bind_repl_SO, llpx_sn_bind/
| #G #Ls #V #T1 #T2 #_ #IHT12 #Ld #H elim (llpx_sn_inv_flat … H) -H
  /3 width=1 by llpx_sn_flat/
| #G #Ls #V #T1 #T2 #_ #IHT12 #Ld #H elim (llpx_sn_inv_flat … H) -H
  /3 width=1 by llpx_sn_flat/
]
qed-.
