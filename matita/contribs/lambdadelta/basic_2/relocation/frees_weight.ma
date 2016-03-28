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

include "ground_2/relocation/rtmap_id.ma".
include "basic_2/grammar/cl_restricted_weight.ma".
include "basic_2/relocation/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

(* Notes: this replaces lemma 1400 concluding the "big tree" theorem *)
lemma frees_total: ∀L,T. ∃f. L ⊢ 𝐅*⦃T⦄ ≡ f.
@(f2_ind … rfw) #n #IH #L *
[ cases L -L /3 width=2 by frees_atom, ex_intro/
  #L #I #V *
  [ #s #Hn destruct elim (IH L (⋆s)) -IH /3 width=2 by frees_sort, ex_intro/
  | * [2: #i ] #Hn destruct
    [ elim (IH L (#i)) -IH /3 width=2 by frees_lref, ex_intro/
    | elim (IH L V) -IH /3 width=2 by frees_zero, ex_intro/
    ]
  | #l #Hn destruct elim (IH L (§l)) -IH /3 width=2 by frees_gref, ex_intro/
  ]
| * [ #p ] #I #V #T #Hn destruct elim (IH L V) // #f1 #HV
  [ elim (IH (L.ⓑ{I}V) T) -IH // #f2 #HT
    elim (sor_isfin_ex f1 (⫱f2))
    /3 width=6 by frees_fwd_isfin, frees_bind, isfin_tl, ex_intro/
  | elim (IH L T) -IH // #f2 #HT
    elim (sor_isfin_ex f1 f2)
    /3 width=6 by frees_fwd_isfin, frees_flat, ex_intro/ 
  ]
]
qed-.
