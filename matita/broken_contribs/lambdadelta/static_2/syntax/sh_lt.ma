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

include "ground/arith/nat_lt_minus.ma".
include "static_2/syntax/sh_props.ma".

(* SORT HIERARCHY ***********************************************************)

(* strict monotonicity condition *)
record sh_lt (h): Prop ≝
{
  sh_next_lt: ∀s. s < ⇡[h]s
}.

(* Basic properties *********************************************************)

lemma sh_nexts_le (h): sh_lt h → ∀s,n. s ≤ ⇡*[h,n]s.
#h #Hh #s #n @(nat_ind_succ … n) -n [ // ] #n #IH <sh_nexts_succ
lapply (sh_next_lt … Hh (⇡*[h,n]s)) #H
lapply (nle_nlt_trans … IH H) -IH -H /2 width=2 by nlt_des_le/
qed.

lemma sh_nexts_lt (h): sh_lt h → ∀s,n. s < ⇡*[h,⁤↑n]s.
#h #Hh #s #n <sh_nexts_succ
lapply (sh_nexts_le … Hh s n) #H
@(nle_nlt_trans … H) /2 width=1 by sh_next_lt/
qed.

lemma sh_lt_nexts_inv_lt (h): sh_lt h →
      ∀s,n1,n2. ⇡*[h,n1]s < ⇡*[h,n2]s → n1 < n2.
#h #Hh
@pull_2 #n1
@(nat_ind_succ … n1) -n1
[ #s #n2 @(nat_ind_succ … n2) -n2
  [ #H elim (nlt_inv_refl … H)
  | #n2 #_ //
  ]
| #n1 #IH #s #n2 @(nat_ind_succ … n2) -n2
  [ <sh_nexts_zero #H
    elim (nlt_inv_refl s)
    /3 width=3 by sh_nexts_lt, nlt_trans/
  | #n2 #_ <sh_nexts_succ_next <sh_nexts_succ_next #H
    /3 width=2 by nlt_succ_bi/
  ]
]
qed-.

lemma sh_lt_acyclic (h): sh_lt h → sh_acyclic h.
#h #Hh
@mk_sh_acyclic
@pull_2 #n1
@(nat_ind_succ … n1) -n1
[ #s #n2 @(nat_ind_succ … n2) -n2 [ // ] #n2 #_ <sh_nexts_zero #H
  elim (nlt_inv_refl s) >H in ⊢ (??%); -H
  /2 width=1 by sh_nexts_lt/
| #n1 #IH #s #n2 @(nat_ind_succ … n2) -n2
  [ <sh_nexts_zero #H -IH
    elim (nlt_inv_refl s) <H in ⊢ (??%); -H
    /2 width=1 by sh_nexts_lt/
  | #n2 #_ <sh_nexts_succ_next <sh_nexts_succ_next #H
    lapply (IH … H) -IH -H //
  ]
]
qed.

lemma sh_lt_dec (h): sh_lt h → sh_decidable h.
#h #Hh
@mk_sh_decidable #s1 #s2
elim (nat_split_lt_ge s2 s1) #Hs
[ @or_intror * #n #H destruct
  @(nlt_ge_false … Hs) /2 width=1 by sh_nexts_le/ (**) (* full auto too slow *)
| @(nle_ind_sn … Hs) -s1 -s2 #s1 #s2 #IH #Hs12
  elim (nat_split_lt_eq_gt s2 (⇡[h]s1)) #Hs21 destruct
  [ elim (nle_split_lt_eq … Hs12) -Hs12 #Hs12 destruct
    [ -IH @or_intror * #n #H destruct
      generalize in match Hs21; -Hs21
      >sh_nexts_unit #H
      lapply (sh_lt_nexts_inv_lt … Hh … H) -H #H
      <(nle_inv_zero_dx n) in Hs12;
      /2 width=2 by nlt_inv_refl, nle_inv_succ_bi/
    | /3 width=2 by ex_intro, or_introl/
    ]
  | -IH @or_introl @(ex_intro … (⁤𝟏)) // (**) (* auto fails *)
  | lapply (nlt_trans s1 ??? Hs21) [ /2 width=1 by sh_next_lt/ ] -Hs12 #Hs12
    elim (IH (s2-⇡[h]s1)) -IH
    [3: /3 width=1 by sh_next_lt, nlt_minus_bi_sn/ ]
    <nminus_minus_dx_refl_sn [2,4: /2 width=1 by nlt_des_le/ ] -Hs21
    [ * #n #H destruct
      @or_introl @(ex_intro … (⁤↑n)) //
    | #H1 @or_intror * #n #H2 @H1 -H1 destruct
      generalize in match Hs12; -Hs12
      >(sh_nexts_zero h s1) in ⊢ (?%?→?); #H
      lapply (sh_lt_nexts_inv_lt … Hh … H) -H #H
      >(nlt_des_gen … H) -H
      @(ex_intro … (⫰n)) //
    ]
  ]
]
qed-.
