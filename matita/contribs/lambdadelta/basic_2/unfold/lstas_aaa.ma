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

include "basic_2/static/aaa_lift.ma".
include "basic_2/unfold/lstas_lstas.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* Properties on atomic arity assignment for terms **************************)

lemma aaa_lstas: ∀h,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∀l.
                 ∃∃U. ⦃G, L⦄ ⊢ T •*[h, l] U & ⦃G, L⦄ ⊢ U ⁝ A.
#h #G #L #T #A #H elim H -G -L -T -A
[ /2 width=3 by ex2_intro/
| * #G #L #K #V #B #i #HLK #HV #IHV #l
  [ elim (IHV l) -IHV #W
    elim (lift_total W 0 (i+1))
    lapply (drop_fwd_drop2 … HLK)
    /3 width=10 by lstas_ldef, aaa_lift, ex2_intro/
  | @(nat_ind_plus … l) -l
    [ elim (IHV 0) -IHV /3 width=7 by lstas_zero, aaa_lref, ex2_intro/
    | #l #_ elim (IHV l) -IHV #W
      elim (lift_total W 0 (i+1))
      lapply (drop_fwd_drop2 … HLK)
      /3 width=10 by lstas_succ, aaa_lift, ex2_intro/
    ]
  ]
| #a #G #L #V #T #B #A #HV #_ #_ #IHT #l elim (IHT l) -IHT
  /3 width=7 by lstas_bind, aaa_abbr, ex2_intro/
| #a #G #L #V #T #B #A #HV #_ #_ #IHT #l elim (IHT l) -IHT
  /3 width=6 by lstas_bind, aaa_abst, ex2_intro/
| #G #L #V #T #B #A #HV #_ #_ #IHT #l elim (IHT l) -IHT
  /3 width=6 by lstas_appl, aaa_appl, ex2_intro/
| #G #L #W #T #A #HW #_ #_ #IHT #l elim (IHT l) -IHT
  /3 width=3 by lstas_cast, aaa_cast, ex2_intro/
]
qed-.

lemma lstas_aaa_conf: ∀h,G,L,l. Conf3 … (aaa G L) (lstas h l G L).
#h #G #L #l #A #T #HT #U #HTU
elim (aaa_lstas h … HT l) -HT #X #HTX
lapply (lstas_mono … HTX … HTU) -T //
qed-.
