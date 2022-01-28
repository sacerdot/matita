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

lemma tr_pap_plus (i1) (i2) (f):
      (⇂*[ninj i2]f)@❨i1❩+f@❨i2❩ = f@❨i1+i2❩.
#i1 #i2 elim i2 -i2
[ * #p #f //
| #i #IH * #p #f
  <pplus_succ_dx <tr_pap_succ <tr_pap_succ
  <IH -IH >nsucc_inj //
]
qed.
