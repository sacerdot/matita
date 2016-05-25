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

include "basic_2/s_computation/fqup_weight.ma".
include "basic_2/static/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

(* Note: this replaces lemma 1400 concluding the "big tree" theorem *)
lemma frees_total: ∀L,T. ∃f. L ⊢ 𝐅*⦃T⦄ ≡ f.
#L #T @(fqup_wf_ind_eq … (⋆) L T) -L -T
#G0 #L0 #T0 #IH #G #L *
[ cases L -L /3 width=2 by frees_atom, ex_intro/
  #L #I #V *
  [ #s #HG #HL #HT destruct
    elim (IH G L (⋆s)) -IH /3 width=2 by frees_sort_gen, fqu_fqup, fqu_drop, lifts_sort, ex_intro/
  | * [2: #i ] #HG #HL #HT destruct
    [ elim (IH G L (#i)) -IH /3 width=2 by frees_lref, fqu_fqup, ex_intro/
    | elim (IH G L V) -IH /3 width=2 by frees_zero, fqu_fqup, fqu_lref_O, ex_intro/
    ]
  | #l #HG #HL #HT destruct
    elim (IH G L (§l)) -IH /3 width=2 by frees_gref_gen, fqu_fqup, fqu_drop, lifts_gref, ex_intro/
  ]
| * [ #p ] #I #V #T #HG #HL #HT destruct elim (IH G L V) // #f1 #HV
  [ elim (IH G (L.ⓑ{I}V) T) -IH // #f2 #HT
    elim (sor_isfin_ex f1 (⫱f2))
    /3 width=6 by frees_fwd_isfin, frees_bind, isfin_tl, ex_intro/
  | elim (IH G L T) -IH // #f2 #HT
    elim (sor_isfin_ex f1 f2)
    /3 width=6 by frees_fwd_isfin, frees_flat, ex_intro/ 
  ]
]
qed-.
