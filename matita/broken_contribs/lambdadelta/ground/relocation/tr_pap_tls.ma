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

include "ground/relocation/tr_pap.ma".
include "ground/lib/stream_tls.ma".

(* POSITIVE APPLICATION FOR TOTAL RELOCATION MAPS ***************************)

(* Constructions with stream_tls ********************************************)

lemma tr_pap_plus (p1) (p2:ℤ⁺) (f):
      (⇂*[p2]f)＠⧣❨p1❩+f＠⧣❨p2❩ = f＠⧣❨p1+p2❩.
#p1 #p2 elim p2 -p2
[ * #p #f //
| #i #IH * #p #f
  <pplus_succ_dx <tr_cons_pap_succ <tr_cons_pap_succ
  <IH -IH //
]
qed.
