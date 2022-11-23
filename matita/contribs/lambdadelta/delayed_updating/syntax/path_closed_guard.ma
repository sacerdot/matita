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

include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_guard.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

axiom list_ind_pippo (A) (Q:predicate …):
      (∀l. (∀m. (∃p. p⨁{A}m = l) → Q m) → Q l) → ∀l. Q l.

(* Destructions with pgc ****************************************************)

lemma path_closed_des_guard (x) (n):
      x ϵ 𝐂❨Ⓕ,n❩ →
      ∃∃p,q. p ϵ 𝐆 & q ϵ 𝐂❨Ⓕ,𝟎❩ & p●q = x.
#x @(list_ind_pippo … x) -x
#x #IH #n #H0 @(insert_eq_1 … x … H0) -H0
#y * -y -n
[|*: #y #n [ #k #_ ] #Hy ] #H0 destruct
[ /2 width=5 by pgc_empty, pcc_empty, ex3_2_intro/
| elim (pcc_false_inv_append_bi … Hy) -Hy #r #s #Hr #Hs #H0 destruct
  elim (IH … Hr) -IH -Hr [| /2 width=2 by ex_intro/ ]
  #p #q #Hp #Hq #H0 destruct
  @(ex3_2_intro … Hp) -Hp [1,3: // ]
  /3 width=2 by pcc_append_bi, pcc_false_d_dx/
| elim (IH … Hy) -IH -Hy [| /2 width=2 by ex_intro/ ]
  #p #q #Hp #Hq #H0 destruct
  /3 width=5 by pcc_m_dx, ex3_2_intro/
| @(ex3_2_intro … (y◖𝗟) (𝐞)) //
| elim (IH … Hy) -IH -Hy [| /2 width=2 by ex_intro/ ]
  #p #q #Hp #Hq #H0 destruct
  /3 width=5 by pcc_A_dx, ex3_2_intro/
| elim (IH … Hy) -IH -Hy [| /2 width=2 by ex_intro/ ]
  #p #q #Hp #Hq #H0 destruct
  /3 width=5 by pcc_S_dx, ex3_2_intro/
]
qed-.
