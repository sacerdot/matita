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

(* Constructions with tr_compose and tr_next ********************************)

lemma tr_compose_uni_unit_sn (f):
      āf ā š®āØšā©āf.
#f >nsucc_zero <tr_uni_succ //
qed.

(* Constructions with tr_compose and tr_tl **********************************)

lemma tr_tl_compose_uni_sn (n) (f):
      āf ā ā(š®āØnā©āf).
#n @(nat_ind_succ ā¦ n) -n //
/2 width=1 by stream_tl_eq_repl/
qed.

(* Constructions with tr_compose and tr_tls *********************************)

lemma tr_tls_compose_uni_sn (f) (n) (p:pnat):
      ā*[p]f ā ā*[p](š®āØnā©āf).
#f #n #p elim p -p //
#p #IH /2 width=1 by stream_tl_eq_repl/
qed.

lemma tr_tl_compose_uni_dx (f) (n):
      ā*[ān]f ā ā(fāš®āØnā©).
// qed.

lemma tr_tls_compose_uni_dx (f) (p) (n):
      ā*[p+n]f ā ā*[p](fāš®āØnā©).
#f #p elim p -p [| #p #IH ] #n
[ <nrplus_unit_sn //
| <nrplus_succ_sn >nsucc_inj >nsucc_inj
  /2 width=3 by stream_tl_eq_repl/
]
qed.

(* Main constructions with tr_compose and tr_tls ****************************)

theorem tr_compose_uni_dx_pap (f) (p):
        (š®āØfļ¼ ā§£āØpā©ā©āā*[p]f) ā fāš®āØpā©.
#f #p
@nstream_eq_inv_ext #q
<tr_compose_pap <tr_compose_pap
<tr_uni_pap <tr_uni_pap
<tr_pap_plus //
qed.
