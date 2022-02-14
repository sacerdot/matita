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

include "ground/relocation/tr_uni_pap.ma".
include "ground/relocation/tr_id_compose.ma".
include "ground/relocation/tr_compose_pn.ma".
include "ground/lib/stream_hdtl_eq.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS *******************************)

(* Constructions with tr_compose and tr_tl **********************************)

lemma tr_tl_compose_uni_sn (n) (f):
      ⇂f ≗ ⇂(𝐮❨n❩∘f).
#n @(nat_ind_succ … n) -n //
/2 width=1 by stream_tl_eq_repl/
qed.

(* Constructions with tr_compose and tr_tls *********************************)

lemma tr_tl_compose_uni_dx (f) (n):
      ⇂*[↑n]f ≗ ⇂(f∘𝐮❨n❩).
// qed.

lemma tr_tls_compose_uni_dx (f) (p) (n):
      ⇂*[p+n]f ≗ ⇂*[p](f∘𝐮❨n❩).
#f #p elim p -p [| #p #IH ] #n
[ <nrplus_unit_sn //
| <nrplus_succ_sn >nsucc_inj >nsucc_inj
  /2 width=3 by stream_tl_eq_repl/
]
qed.

(* Main constructions with tr_compose and tr_tls ****************************)

theorem tr_compose_uni_dx (f) (p):
        (𝐮❨f@❨p❩❩∘⇂*[p]f ≗ f∘𝐮❨p❩).
#f #p
@nstream_eq_inv_ext #q
<tr_compose_pap <tr_compose_pap
<tr_uni_pap <tr_uni_pap
<tr_pap_plus //
qed.
