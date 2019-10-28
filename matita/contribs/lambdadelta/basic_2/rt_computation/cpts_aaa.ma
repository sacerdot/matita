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

include "static_2/static/aaa.ma".
include "basic_2/rt_computation/cpts_drops.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-COMPUTATION FOR TERMS ***************)

(* Properties with atomic arity assignment for terms ************************)

lemma cpts_total_aaa (h) (G) (L) (T1):
      ∀A. ⦃G,L⦄ ⊢ T1 ⁝ A → ∀n. ∃T2. ⦃G,L⦄ ⊢ T1 ⬆*[h,n] T2.
#h #G #L #T1 #A #H elim H -G -L -T1 -A
[ #G #L #s #n /3 width=2 by ex_intro/
| #I #G #K #V1 #B #_ #IH #n -B
  cases I -I
  [ elim (IH n) -IH #V2 #HV12
    elim (lifts_total V2 (𝐔❴1❵)) #T2 #HVT2
    /3 width=4 by cpts_delta, ex_intro/
  | cases n -n
    [ /2 width=2 by ex_intro/
    | #n elim (IH n) -IH #V2 #HV12
      elim (lifts_total V2 (𝐔❴1❵)) #T2 #HVT2
      /3 width=4 by cpts_ell, ex_intro/
    ]
  ]
| #I #G #K #A #i #_ #IH #n -A
  elim (IH n) -IH #T #HT
  elim (lifts_total T (𝐔❴1❵)) #U #HTU
  /3 width=4 by cpts_lref, ex_intro/
| #p #G #L #V1 #T1 #B #A #_ #_ #IHV #IHT #n -B -A
  elim (IHV 0) -IHV #V2 #HV12
  elim (IHT n) -IHT #T2 #HT12
  /3 width=3 by cpts_bind_dx, ex_intro/
| #p #G #L #V1 #T1 #B #A #_ #_ #IHV #IHT #n -B -A
  elim (IHV 0) -IHV #V2 #HV12
  elim (IHT n) -IHT #T2 #HT12
  /3 width=3 by cpts_bind_dx, ex_intro/
| #G #L #V1 #T1 #B #A #_ #_ #IHV #IHT #n -B -A
  elim (IHV 0) -IHV #V2 #HV12
  elim (IHT n) -IHT #T2 #HT12
  /3 width=3 by cpts_appl_dx, ex_intro/
| #G #L #U1 #T1 #A #_ #_ #IHU #_ #n -A
  cases n -n
  [ /2 width=2 by ex_intro/
  | #n elim (IHU n) -IHU #U2 #HU12
    /3 width=3 by cpts_ee, ex_intro/
  ]
]
qed-.
