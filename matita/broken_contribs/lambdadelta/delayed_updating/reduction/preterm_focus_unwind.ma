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

include "delayed_updating/unwind/unwind2_preterm_eq.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/reduction/prototerm_focus.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

(* Constructions with unwind ************************************************)

lemma brf_unwind (f) (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      ▼[f]t ∩ 𝐅❨⊗p,⊗b,⊗q❩ ⇔ ▼[f](t ∩ 𝐅❨p,b,q❩).
#f #t #r #p #b #q #n #Ht #H0
lapply (xprc_des_n … H0) -H0 #Hn
<brf_unfold <brf_unfold
/2 width=2 by unwind2_slice_and_sn/
qed.
